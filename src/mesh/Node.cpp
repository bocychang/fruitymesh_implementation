////////////////////////////////////////////////////////////////////////////////
// /****************************************************************************
// **
// ** Copyright (C) 2015-2022 M-Way Solutions GmbH
// ** Contact: https://www.blureange.io/licensing
// **
// ** This file is part of the Bluerange/FruityMesh implementation
// **
// ** $BR_BEGIN_LICENSE:GPL-EXCEPT$
// ** Commercial License Usage
// ** Licensees holding valid commercial Bluerange licenses may use this file in
// ** accordance with the commercial license agreement provided with the
// ** Software or, alternatively, in accordance with the terms contained in
// ** a written agreement between them and M-Way Solutions GmbH. 
// ** For licensing terms and conditions see https://www.bluerange.io/terms-conditions. For further
// ** information use the contact form at https://www.bluerange.io/contact.
// **
// ** GNU General Public License Usage
// ** Alternatively, this file may be used under the terms of the GNU
// ** General Public License version 3 as published by the Free Software
// ** Foundation with exceptions as appearing in the file LICENSE.GPL3-EXCEPT
// ** included in the packaging of this file. Please review the following
// ** information to ensure the GNU General Public License requirements will
// ** be met: https://www.gnu.org/licenses/gpl-3.0.html.
// **
// ** $BR_END_LICENSE$
// **
// ****************************************************************************/
////////////////////////////////////////////////////////////////////////////////

#include <Config.h>

#include <Node.h>
#include <LedWrapper.h>
#include <AdvertisingController.h>
#include <GAPController.h>
#include <GlobalState.h>
#include <GATTController.h>
#include <ConnectionManager.h>
#include <ScanController.h>
#include <Utility.h>
#include <Logger.h>
#include <StatusReporterModule.h>
#include <MeshConnection.h>
#include <MeshAccessConnection.h>
#include "ConnectionMessageTypes.h"
#include "MeshAccessModule.h"
#include "PrimitiveTypes.h"
#include "mini-printf.h"

#if IS_ACTIVE(SIG_MESH)
#include <SigAccessLayer.h>
#endif

#include <ctime>
#include <cmath>
#include <cstdlib>

#ifdef SIM_ENABLED
#include <CherrySim.h>    //required for faking DFU
#endif

//The number of connection attempts to one node before blacklisting this node for some time
constexpr u8 connectAttemptsBeforeBlacklisting = 5;

// The Service that is used for two nodes to communicate between each other
// Fruity Mesh Service UUID 310bfe40-ed6b-11e3-a1be-0002a5d5c51b
constexpr u8 MESH_SERVICE_BASE_UUID128[] = { 0x23, 0xD1, 0xBC, 0xEA, 0x5F, 0x78, 0x23, 0x15, 0xDE, 0xEF, 0x12, 0x12, 0x00, 0x00, 0x00, 0x00 };
constexpr u16 MESH_SERVICE_CHARACTERISTIC_UUID = 0x1524;

//new: 全域變數定義（使用 static 避免外部連結衝突）
static NodeId root;
static int init = -1;  //初始化
static int numNodes = -1; //Node數
static int flag = -1; // 開關用
static int counta = 0; // 測試關閉啟用count數
static int testdis = 0;
//new: avg delay
static u8 TOTAL_NODE_NUM = -1;//nnber 注意 17

// 注意：統計陣列定義為 static，避免影響類別對齊
static u32 avgDelay[16];          // 平均延遲
static u32 rcvCountArray[16];     // 接收計數陣列
static u32 MultipleCountArray[16];// 多次傳輸計數陣列
static u32 CollsndCountArray[16]; // 碰撞傳送計數陣列
static u32 avgDelayHighPrio[16];  // HIGH priority 平均延遲
static u32 avgDelayLowPrio[16];   // LOW priority 平均延遲
static u32 rcvCountHighPrio[16];  // HIGH priority 接收計數
static u32 rcvCountLowPrio[16];   // LOW priority 接收計數
static u32 sndCountHighPrio[16];  // HIGH priority 發送計數
static u32 sndCountLowPrio[16];   // LOW priority 發送計數
static u32 generateLoadHighActualSent;  // 實際發送 HIGH 數量（含重傳）
static u32 generateLoadLowActualSent;   // 實際發送 LOW 數量（含重傳
static const char* cmd[16];

static int ssettime = -1; // ssettime 開關
static int delayTime = -1; // delayTime 開關
static int adjust = -1; //調整誤差 開關
static int errorIndex = 0; //誤差值

static bool delayReporter = false; //default reporter delay
static bool switchReporter = false; //default

static bool generate_load = false; //default generate load  


Node::Node()
    : Module(ModuleId::NODE, "node")
{
    CheckedMemset(&meshService, 0, sizeof(meshService));

    //Save configuration to base class variables
    //sizeof configuration must be a multiple of 4 bytes
    configurationPointer = &configuration;
    configurationLength = sizeof(NodeConfiguration);
}

void Node::Init()
{
    //Load default configuration
    ResetToDefaultConfiguration();
    isInit = true;
}

bool Node::IsInit()
{
    return isInit;
}

void Node::ResetToDefaultConfiguration()
{
    configuration.moduleId = ModuleId::NODE;
    configuration.moduleVersion = NODE_MODULE_CONFIG_VERSION;
    configuration.moduleActive = true;

    //Load defaults from Config
    configuration.enrollmentState = RamConfig->defaultNetworkId != 0 ? EnrollmentState::ENROLLED : EnrollmentState::NOT_ENROLLED;
    configuration.nodeId = RamConfig->defaultNodeId;
    configuration.networkId = RamConfig->defaultNetworkId;
    CheckedMemcpy(configuration.networkKey, RamConfig->defaultNetworkKey, 16);
    CheckedMemcpy(configuration.userBaseKey, RamConfig->defaultUserBaseKey, 16);

    CheckedMemcpy(&configuration.bleAddress, &RamConfig->staticAccessAddress, sizeof(FruityHal::BleGapAddr));
    configuration.numberOfEnrolledDevices = 0;

    CheckedMemset(configuration.dynamicGroupIds, 0, sizeof(configuration.dynamicGroupIds));

    SET_FEATURESET_CONFIGURATION(&configuration, this);
}

void Node::ConfigurationLoadedHandler(u8* migratableConfig, u16 migratableConfigLength)
{
    //We must now decide if we want to overwrite some unset persistent config values with defaults
    if(configuration.nodeId == 0) configuration.nodeId = RamConfig->defaultNodeId;
    if(configuration.networkId == 0) configuration.networkId = RamConfig->defaultNetworkId;
    if(Utility::CompareMem(0x00, configuration.networkKey, 16)){
        CheckedMemcpy(configuration.networkKey, RamConfig->defaultNetworkKey, 16);
    }
    if(Utility::CompareMem(0x00, configuration.userBaseKey, 16)){
        CheckedMemcpy(configuration.userBaseKey, RamConfig->defaultUserBaseKey, 16);
    }

    //In case persistence is disabled, we check if there is a temporary enrollment that should be loaded
    if (!GS->config.enableRecordStorage)
    {
        //First, check the CRC of the enrollment and clear it if it is in an in-correct state
        u32 crc32 = Utility::CalculateCrc32((u8*)GS->temporaryEnrollmentPtr, sizeof(TemporaryEnrollment) - sizeof(u32));
        
        //Erase persistent data if there is any available on the device
        if (GS->recordStorage.HasMortalRecords()) {
            GS->recordStorage.LockDownAndClearAllSettings(Utility::GetWrappedModuleId(ModuleId::NODE), this, (u32)NodeSaveActions::FACTORY_RESET);
        }

        if (crc32 == GS->temporaryEnrollmentPtr->crc32) {

            if (GS->temporaryEnrollmentPtr->enrollmentState == EnrollmentState::ENROLLED) {
                GS->node.configuration.enrollmentState = GS->temporaryEnrollmentPtr->enrollmentState;
                GS->node.configuration.nodeId = GS->temporaryEnrollmentPtr->nodeId;
                GS->node.configuration.networkId = GS->temporaryEnrollmentPtr->networkId;
                CheckedMemcpy(GS->node.configuration.networkKey, GS->temporaryEnrollmentPtr->networkKey, sizeof(GS->temporaryEnrollmentPtr->networkKey));
                CheckedMemcpy(GS->node.configuration.userBaseKey, GS->temporaryEnrollmentPtr->userBaseKey, sizeof(GS->temporaryEnrollmentPtr->userBaseKey));
                CheckedMemcpy(GS->node.configuration.organizationKey, GS->temporaryEnrollmentPtr->organizationKey, sizeof(GS->temporaryEnrollmentPtr->organizationKey));
            }

            if (GS->temporaryEnrollmentPtr->serialNumberIndex != 0) {
                GS->config.configuration.isSerialNumberIndexOverwritten = true;
                GS->config.configuration.overwrittenSerialNumberIndex = GS->temporaryEnrollmentPtr->serialNumberIndex;
            }

            if (!Utility::CompareMem(0x00, GS->temporaryEnrollmentPtr->nodeKey, sizeof(GS->temporaryEnrollmentPtr->nodeKey))) {
                CheckedMemcpy(GS->config.configuration.nodeKey, GS->temporaryEnrollmentPtr->nodeKey, sizeof(GS->temporaryEnrollmentPtr->nodeKey));
            }
        }
        else {
            CheckedMemset(GS->temporaryEnrollmentPtr, 0x00, sizeof(TemporaryEnrollment));
        }
    }

    //Random offset that can be used to disperse packets from different nodes over time
    GS->appTimerRandomOffsetDs = (configuration.nodeId % 100);

    //Change window title of the Terminal
    SetTerminalTitle();
    logt("NODE", "====> Node %u (%s) <====", configuration.nodeId, RamConfig->GetSerialNumber());

    //Get a random number for the connection loss counter (hard on system start,...stat)
    randomBootNumber = Utility::GetRandomInteger();

    clusterId = this->GenerateClusterID();

    //Set the BLE address so that we have the same on every startup, mostly for debugging
    if(configuration.bleAddress.addr_type != FruityHal::BleGapAddrType::INVALID){
        ErrorType err = FruityHal::SetBleGapAddress(configuration.bleAddress);
        if(err != ErrorType::SUCCESS){
            //Can be ignored and will not happen
        }
    }

    //Print configuration and start node
    logt("NODE", "Config loaded nodeId:%d, connLossCount:%u, networkId:%d", configuration.nodeId, connectionLossCounter, configuration.networkId);

    //Register the mesh service in the GATT table
    InitializeMeshGattService();

    //Remove Advertising job if it's been registered before
    GS->advertisingController.RemoveJob(meshAdvJobHandle);
    meshAdvJobHandle = nullptr;


    if(GET_DEVICE_TYPE() != DeviceType::ASSET && configuration.networkId != 0){
        //Register Job with AdvertisingController
        AdvJob job = {
            AdvJobTypes::SCHEDULED,
            5, //Slots
            0, //Delay
            MSEC_TO_UNITS(100, CONFIG_UNIT_0_625_MS), //AdvInterval
            0, //AdvChannel
            0, //CurrentSlots
            0, //CurrentDelay
            FruityHal::BleGapAdvType::ADV_IND, //Advertising Mode
            {0}, //AdvData
            0, //AdvDataLength
            {0}, //ScanData
            0 //ScanDataLength
        };
        meshAdvJobHandle = GS->advertisingController.AddJob(job);

        //Go to Discovery if node is active
        //Fill JOIN_ME packet with data
        this->UpdateJoinMePacket();

        ChangeState(DiscoveryState::HIGH);
    }
}

void Node::InitializeMeshGattService()
{
    u32 err = 0;

    //##### At first, we register our custom service
    //Add our Service UUID to the BLE stack for management
    err = (u32)FruityHal::BleUuidVsAdd(MESH_SERVICE_BASE_UUID128, &meshService.serviceUuid.type);
    FRUITYMESH_ERROR_CHECK(err); //OK

    //Add the service
    err = (u32)FruityHal::BleGattServiceAdd(FruityHal::BleGattSrvcType::PRIMARY, meshService.serviceUuid, &meshService.serviceHandle);
    FRUITYMESH_ERROR_CHECK(err); //OK

    //##### Now we need to add a characteristic to that service

    //BLE GATT Attribute Metadata http://developer.nordicsemi.com/nRF51_SDK/doc/7.1.0/s120/html/a00163.html
    //Read and write permissions, variable length, etc...
    FruityHal::BleGattAttributeMetadata attributeMetadata;
    CheckedMemset(&attributeMetadata, 0, sizeof(attributeMetadata));

    //If encryption is enabled, we want our mesh handle only to be accessable over an
    //encrypted connection with authentication
    if(Conf::encryptionEnabled){
        FH_CONNECTION_SECURITY_MODE_SET_ENC_NO_MITM(&attributeMetadata.readPerm);
        FH_CONNECTION_SECURITY_MODE_SET_ENC_NO_MITM(&attributeMetadata.writePerm);
    }
    else
    {
        FH_CONNECTION_SECURITY_MODE_SET_OPEN(&attributeMetadata.readPerm);
        FH_CONNECTION_SECURITY_MODE_SET_OPEN(&attributeMetadata.writePerm);
    }

    attributeMetadata.valueLocation = FH_BLE_GATTS_VALUE_LOCATION_STACK; //We currently have the value on the SoftDevice stack, we might port that to the application space
    attributeMetadata.readAuthorization = 0;
    attributeMetadata.writeAuthorization = 0;
    attributeMetadata.variableLength = 1; //Make it a variable length attribute

    //Characteristic metadata, whatever....
    FruityHal::BleGattCharMd characteristicMetadata;
    CheckedMemset(&characteristicMetadata, 0, sizeof(characteristicMetadata));
    characteristicMetadata.charProperties.read = 1; /*Reading value permitted*/
    characteristicMetadata.charProperties.write = 1; /*Writing value with Write Request permitted*/
    characteristicMetadata.charProperties.writeWithoutResponse = 1; /*Writing value with Write Command permitted*/
    characteristicMetadata.charProperties.authSignedWrite = 0; /*Writing value with Signed Write Command not permitted*/
    characteristicMetadata.charProperties.notify = 1; /*Notications of value permitted*/
    characteristicMetadata.charProperties.indicate = 0; /*Indications of value not permitted*/
    characteristicMetadata.p_cccdMd = nullptr;

    //Finally, the attribute
    FruityHal::BleGattAttribute attribute;
    CheckedMemset(&attribute, 0, sizeof(attribute));

    FruityHal::BleGattUuid attributeUUID;
    attributeUUID.type = meshService.serviceUuid.type;
    attributeUUID.uuid = MESH_SERVICE_CHARACTERISTIC_UUID;

    attribute.p_uuid = &attributeUUID; /* The UUID of the Attribute*/
    attribute.p_attributeMetadata = &attributeMetadata; /* The previously defined attribute Metadata */
    attribute.maxLen = MESH_CHARACTERISTIC_MAX_LENGTH;
    attribute.initLen = 0;
    attribute.initOffset = 0;

    //Finally, add the characteristic
    err = (u32)FruityHal::BleGattCharAdd(meshService.serviceHandle, characteristicMetadata, attribute, meshService.sendMessageCharacteristicHandle);
    FRUITYMESH_ERROR_CHECK(err); //OK
}


/*
 #########################################################################################################
 ### Connections and Handlers
 #########################################################################################################
 */
#define ________________CONNECTION___________________

//Is called after a connection has ended its handshake
void Node::HandshakeDoneHandler(MeshConnection* connection, bool completedAsWinner)
{
    logt("HANDSHAKE", "############ Handshake done (asWinner:%u) ###############", completedAsWinner);

    StatusReporterModule* statusMod = (StatusReporterModule*)GS->node.GetModuleById(ModuleId::STATUS_REPORTER_MODULE);
    if(statusMod != nullptr){
        statusMod->SendLiveReport(LiveReportTypes::MESH_CONNECTED, 0, connection->partnerId, completedAsWinner);
    }

    GS->logger.LogCustomCount(CustomErrorTypes::COUNT_HANDSHAKE_DONE);

    //We delete the joinMe packet of this node from the join me buffer
    for (u32 i = 0; i < joinMePackets.size(); i++)
    {
        joinMeBufferPacket* packet = &joinMePackets[i];
        if (packet->payload.sender == connection->partnerId) {
            CheckedMemset(packet, 0x00, sizeof(joinMeBufferPacket));
        }
    }

    //We can now commit the changes that were part of the handshake
    //This node was the winner of the handshake and successfully acquired a new member
    if(completedAsWinner){
        //Update node data
        const ClusterSize cluster = GetClusterSize() + 1;
        SetClusterSize(cluster);
        connection->hopsToSink = connection->clusterAck1Packet.payload.hopsToSink < 0 ? -1 : connection->clusterAck1Packet.payload.hopsToSink + 1;

        logt("HANDSHAKE", "ClusterSize Change from %d to %d", GetClusterSize()-1, GetClusterSize());

        //Update connection data
        connection->connectedClusterId = connection->clusterIDBackup;
        connection->partnerId = connection->clusterAck1Packet.header.sender;
        connection->connectedClusterSize = 1;

        //Broadcast cluster update to other connections
        ConnPacketClusterInfoUpdate outPacket;
        CheckedMemset((u8*)&outPacket, 0x00, sizeof(ConnPacketClusterInfoUpdate));

        outPacket.payload.clusterSizeChange = 1;
        outPacket.payload.connectionMasterBitHandover = 0;
        // => hops to sink is set later in SendClusterInfoUpdate

        SendClusterInfoUpdate(connection, &outPacket);

    //This node was the looser of the Handshake and is now part of a newer bigger cluster
    } else {

        //The node that receives this message can not be connected to any other node
        //This is why we can set absolute values for the clusterSize
        connection->connectedClusterId = connection->clusterAck2Packet.payload.clusterId;
        connection->connectedClusterSize = connection->clusterAck2Packet.payload.clusterSize - 1; // minus myself

        //If any cluster updates are waiting, we delete them
        connection->ClearCurrentClusterInfoUpdatePacket();

        clusterId = connection->clusterAck2Packet.payload.clusterId;
        SetClusterSize(connection->clusterAck2Packet.payload.clusterSize); // The other node knows best

        connection->hopsToSink = connection->clusterAck2Packet.payload.hopsToSink < 0 ? -1 : connection->clusterAck2Packet.payload.hopsToSink + 1;

        // We want the bigger cluster to send it's information about enrolled nodes.
        connection->enrolledNodesSynced = true;

        logt("HANDSHAKE", "ClusterSize set to %d", GetClusterSize());
    }

    logjson("CLUSTER", "{\"type\":\"cluster_handshake\",\"winner\":%u,\"size\":%d}" SEP, completedAsWinner, GetClusterSize());

    logjson("SIM", "{\"type\":\"mesh_connect\",\"partnerId\":%u}" SEP, connection->partnerId);

    connection->connectionState = ConnectionState::HANDSHAKE_DONE;
    connection->connectionHandshakedTimestampDs = GS->appTimerDs;

    // Send ClusterInfo again as the amount of hops to the sink will have changed
    // after this connection is in the handshake done state
    // TODO: This causes an increase in cluster info update packets. It is possible to combine this with
    //the cluster update above, but that requires more debugging to get it correctly working
    SendClusterInfoUpdate(connection, nullptr);

    //Call our lovely modules
    for(u32 i=0; i<GS->amountOfModules; i++){
        if(GS->activeModules[i]->configurationPointer->moduleActive){
            GS->activeModules[i]->MeshConnectionChangedHandler(*connection);
        }
    }

    //Update our advertisement packet
    UpdateJoinMePacket();

    //Pass on the masterbit to someone if necessary
    HandOverMasterBitIfNecessary();
}

MeshAccessAuthorization Node::CheckMeshAccessPacketAuthorization(BaseConnectionSendData * sendData, u8 const * data, FmKeyId fmKeyId, DataDirection direction)
{
    ConnPacketHeader const * packet = (ConnPacketHeader const *)data;

    if (
        (
            // NOT FmKeyId::NODE as we don't want to leak information from the mesh
            // that is sent to broadcast if we are only connected with FmKeyId::NODE.
            fmKeyId == FmKeyId::ORGANIZATION
         || fmKeyId == FmKeyId::NETWORK
        )
        && direction == DataDirection::DIRECTION_OUT)
    {
        return MeshAccessAuthorization::WHITELIST;
    }
    if (   packet->messageType == MessageType::MODULE_RAW_DATA
        || packet->messageType == MessageType::MODULE_RAW_DATA_LIGHT)
    {
        if (fmKeyId == FmKeyId::NETWORK)
        {
            return MeshAccessAuthorization::WHITELIST;
        }
        else if (fmKeyId == FmKeyId::NODE)
        {
            return MeshAccessAuthorization::LOCAL_ONLY;
        }
    }
    if (packet->messageType == MessageType::CLUSTER_INFO_UPDATE)
    {
        if (fmKeyId == FmKeyId::NETWORK)
        {
            return MeshAccessAuthorization::WHITELIST;
        }
        else
        {
            return MeshAccessAuthorization::UNDETERMINED;
        }
    }
    if (packet->messageType == MessageType::UPDATE_TIMESTAMP || packet->messageType == MessageType::TIME_SYNC)
    {
        //Don't allow the time to be set if it's already set and we didn't receive this message via FM_KEY_ID_NETWORK.
        //Note: FM_KEY_ID_NODE is not sufficient, as the time is a property of the mesh by design.
        if (GS->timeManager.IsTimeSynced() && fmKeyId != FmKeyId::NETWORK)
        {
            return MeshAccessAuthorization::BLACKLIST;
        }
        else
        {
            return MeshAccessAuthorization::WHITELIST;
        }
    }
    if (   packet->messageType == MessageType::COMPONENT_SENSE
        || packet->messageType == MessageType::CAPABILITY)
    {
        if (fmKeyId == FmKeyId::ORGANIZATION)
        {
            return MeshAccessAuthorization::WHITELIST;
        }
    }
    return MeshAccessAuthorization::UNDETERMINED;
}

//TODO: part of the connection manager
//void Node::HandshakeTimeoutHandler()
//{
//    logt("HANDSHAKE", "############ Handshake TIMEOUT/FAIL ###############");
//
//    //Disconnect the hanging connection
//    BaseConnections conn = GS->cm.GetBaseConnections(ConnectionDirection::INVALID);
//    for(int i=0; i<conn.count; i++){
//        if(conn.connections[i]->IsConnected() && !conn.connections[i]->HandshakeDone()){
//            u32 handshakeTimePassed = GS->appTimerDs - conn.connections[i]->handshakeStartedDs;
//            logt("HANDSHAKE", "Disconnecting conn %u, timePassed:%u", conn.connections[i]->connectionId, handshakeTimePassed);
//            conn.connections[i]->Disconnect();
//        }
//    }
//
//    //Go back to discovery
//    ChangeState(discoveryState::DISCOVERY);
//}


void Node::MeshConnectionDisconnectedHandler(AppDisconnectReason appDisconnectReason, ConnectionState connectionStateBeforeDisconnection, u8 hadConnectionMasterBit, i16 connectedClusterSize, u32 connectedClusterId)
{
    logt("NODE", "MeshConn Disconnected with previous state %u", (u32)connectionStateBeforeDisconnection);

    //TODO: If the local host disconnected this connection, it was already increased, we do not have to count the disconnect here
    this->connectionLossCounter++;

    //If the handshake was already done, this node was part of our cluster
    //If the local host terminated the connection, we do not count it as a cluster Size change
    if (
        connectionStateBeforeDisconnection >= ConnectionState::HANDSHAKE_DONE
    ){
        //CASE 1: if our partner has the connection master bit, we must dissolve
        //It may happen rarely that the connection master bit was just passed over and that neither node has it
        //This will result in two clusters dissolving
        if (!hadConnectionMasterBit)
        {
            //FIXME: Workaround to not clean up the wrong connections because in this case, all connections are already cleaned up
            if (appDisconnectReason != AppDisconnectReason::I_AM_SMALLER) {
                GS->cm.ForceDisconnectOtherMeshConnections(nullptr, AppDisconnectReason::PARTNER_HAS_MASTERBIT);
            }

            SetClusterSize(1);
            clusterId = GenerateClusterID();


            SendClusterInfoUpdate(nullptr, nullptr);
        }

        //CASE 2: If we have the master bit, we keep our ClusterId (happens if we are the biggest cluster)
        else
        {
            logt("HANDSHAKE", "ClusterSize Change from %d to %d", GetClusterSize(), GetClusterSize() - connectedClusterSize);

            ClusterSize cluster = GetClusterSize();
            cluster -= connectedClusterSize;
            SetClusterSize(cluster);

            // Inform the rest of the cluster of our new size
            ConnPacketClusterInfoUpdate packet;
            CheckedMemset((u8*)&packet, 0x00, sizeof(ConnPacketClusterInfoUpdate));

            packet.payload.clusterSizeChange = -connectedClusterSize;

            SendClusterInfoUpdate(nullptr, &packet);

        }

        logjson("CLUSTER", "{\"type\":\"cluster_disconnect\",\"size\":%d}" SEP, GetClusterSize());

    }
    //Handshake had not yet finished, not much to do
    else
    {

    }

    //To be sure we do not have a clusterId clash if we are disconnected, we generate one if we are a single node, shouldn't hurt
    //Note that the check has to be based on the amount of MeshConnections, clusterSize is not sufficient as some MeshConnection
    //might still be handshaking.
    if (GS->cm.GetConnectionsOfType(ConnectionType::FRUITYMESH, ConnectionDirection::INVALID).count == 0)
    {
        clusterId = GenerateClusterID();
    }

    //In either case, we must update our advertising packet
    UpdateJoinMePacket();

    //Pass on the masterbit to someone if necessary
    HandOverMasterBitIfNecessary();

    //Revert to discovery high
    // FIXME: is it needed?
    noNodesFoundCounter = 0;
}

//Handles incoming cluster info update
void Node::ReceiveClusterInfoUpdate(MeshConnection* connection, ConnPacketClusterInfoUpdate const * packet)
{
    //Check if next expected counter matches, if not, this clusterUpdate was a duplicate and we ignore it (might happen during reconnection)
    if (connection->nextExpectedClusterUpdateCounter == packet->payload.counter) {
        connection->nextExpectedClusterUpdateCounter++;
    }
    else {
        //This must not happen normally, only in rare cases where the connection is reestablished and the remote node receives a duplicate of the cluster update message
        SIMSTATCOUNT("ClusterUpdateCountMismatch");
        logt("WARNING", "Next expected ClusterUpdateCounter did not match");
        GS->logger.LogCustomError(CustomErrorTypes::WARN_CLUSTER_UPDATE_FLOW_MISMATCH, connection->partnerId);
        return;
    }

    SIMSTATCOUNT("ClusterUpdateCount");

    //Prepare cluster update packet for other connections
    ConnPacketClusterInfoUpdate outPacket;
    CheckedMemset((u8*)&outPacket, 0x00, sizeof(ConnPacketClusterInfoUpdate));
    outPacket.payload.clusterSizeChange = packet->payload.clusterSizeChange;


    if(packet->payload.clusterSizeChange != 0){
        logt("HANDSHAKE", "ClusterSize Change from %d to %d", this->clusterSize, this->clusterSize + packet->payload.clusterSizeChange);
        ClusterSize cluster = GetClusterSize();
        cluster += packet->payload.clusterSizeChange;
        SetClusterSize(cluster);
        connection->connectedClusterSize += packet->payload.clusterSizeChange;
    }

    //Update hops to sink
    //Another sink may have joined or left the network, update this
    //FIXME: race conditions can cause this to work incorrectly...
    connection->hopsToSink = packet->payload.hopsToSink > -1 ? packet->payload.hopsToSink + 1 : -1;
    
    //Now look if our partner has passed over the connection master bit
    if(packet->payload.connectionMasterBitHandover){
        logt("CONN", "NODE %u RECEIVED MASTERBIT FROM %u", configuration.nodeId, packet->header.sender);
        connection->connectionMasterBit = 1;
    }

    //Pass on the masterbit to someone else if necessary
    HandOverMasterBitIfNecessary();

    //hops to sink are updated in the send method
    //current cluster id is updated in the send method

    SendClusterInfoUpdate(connection, &outPacket);

    //Log Cluster change to UART
    logjson("CLUSTER", "{\"type\":\"cluster_update\",\"size\":%d,\"newId\":%u,\"masterBit\":%u}" SEP, clusterSize, clusterId, packet->payload.connectionMasterBitHandover);

    //Enable discovery or prolong its state
    KeepHighDiscoveryActive();

    //Update adverting packet
    this->UpdateJoinMePacket();

    //TODO: What happens if:
    /*
     * We send a clusterid update and commit it in our connection arm
     * The other one does the same at nearly the same time
     * ID before was 3, A now has 2 and 2 on the connection arm, B has 4 and 4 on the connection arm
     * Then both will not accept the new ClusterId!!!
     * What if the biggest id will always win?
     */
}

void Node::HandOverMasterBitIfNecessary()  const{
    //If we have all masterbits, we can give 1 at max
    //We do this, if the connected cluster size is bigger than all the other connected cluster sizes summed together
    bool hasAllMasterBits = HasAllMasterBits();
    if (hasAllMasterBits) {
        MeshConnections conns = GS->cm.GetMeshConnections(ConnectionDirection::INVALID);
        for (u32 i = 0; i < conns.count; i++) {
            MeshConnectionHandle conn = conns.handles[i];
            if (conn.IsHandshakeDone() && conn.GetConnectedClusterSize() > GetClusterSize() - conn.GetConnectedClusterSize()) {
                conn.HandoverMasterBit();
            }
        }
    }
}

bool Node::HasAllMasterBits() const {
    MeshConnections conn = GS->cm.GetMeshConnections(ConnectionDirection::INVALID);
    for (u32 i = 0; i < conn.count; i++) {
        MeshConnectionHandle connection = conn.handles[i];
        //Connection must be handshaked, if yes check if we have its masterbit
        if (connection.IsHandshakeDone() && !connection.HasConnectionMasterBit()) {
            return false;
        }
    }
    return true;
}



//Saves a cluster update for all connections (except the one that caused it)
//This update will then be sent by a connection as soon as the connection is ready (HandshakeDone)
void Node::SendClusterInfoUpdate(MeshConnection* ignoreConnection, ConnPacketClusterInfoUpdate* packet) const
{
    MeshConnections conn = GS->cm.GetMeshConnections(ConnectionDirection::INVALID);
    for (u32 i = 0; i < conn.count; i++) {
        if (!conn.handles[i]) continue;

        //Get the current packet
        ConnPacketClusterInfoUpdate* currentPacket = &(conn.handles[i].GetConnection()->currentClusterInfoUpdatePacket);

        if(!conn.handles[i].GetConnection()->IsConnected()) continue;

        //We currently update the hops to sink at all times
        currentPacket->payload.hopsToSink = GS->cm.GetMeshHopsToShortestSink(conn.handles[i].GetConnection());

        if (conn.handles[i].GetConnection() == ignoreConnection) continue;
        
        if (packet != nullptr) {
            currentPacket->payload.clusterSizeChange += packet->payload.clusterSizeChange;
        }
        
        //=> The counter and maybe some other fields are set right before queuing the packet

        logt("HANDSHAKE", "OUT => %u MESSAGE_TYPE_CLUSTER_INFO_UPDATE clustChange:%d, hops:%d", conn.handles[i].GetPartnerId(), currentPacket->payload.clusterSizeChange, currentPacket->payload.hopsToSink);
    }

    HandOverMasterBitIfNecessary();

    //Send the current state of our cluster to all active MeshAccess connections
    MeshAccessConnections conns2 = GS->cm.GetMeshAccessConnections(ConnectionDirection::INVALID);
    for (u32 i = 0; i < conns2.count; i++) {
        MeshAccessConnectionHandle conn = conns2.handles[i];
        if (conn && conn.IsHandshakeDone()) {
            conn.SendClusterState();
        }
    }

    //TODO: If we call FillTransmitBuffers after a timeout, they would accumulate more,...
    GS->cm.FillTransmitBuffers();
}

void Node::MeshMessageReceivedHandler(BaseConnection* connection, BaseConnectionSendData* sendData, ConnPacketHeader const * packetHeader)
{
    //Must call superclass for handling
    Module::MeshMessageReceivedHandler(connection, sendData, packetHeader);

    //If the packet is a handshake packet it will not be forwarded to the node but will be
    //handled in the connection. All other packets go here for further processing
    switch (packetHeader->messageType)
    {
        case MessageType::CLUSTER_INFO_UPDATE:
            if (
                    connection != nullptr
                    && connection->connectionType == ConnectionType::FRUITYMESH)
            {
                ConnPacketClusterInfoUpdate const * packet = (ConnPacketClusterInfoUpdate const *) packetHeader;
                logt("HANDSHAKE", "IN <= %d CLUSTER_INFO_UPDATE sizeChange:%d, hop:%d", connection->partnerId, packet->payload.clusterSizeChange, packet->payload.hopsToSink);
                ReceiveClusterInfoUpdate((MeshConnection*)connection, packet);

            }
            break;
        case MessageType::UPDATE_CONNECTION_INTERVAL:
            {
                ConnPacketUpdateConnectionInterval const * packet = (ConnPacketUpdateConnectionInterval const *) packetHeader;

                GS->cm.SetMeshConnectionInterval(packet->newInterval);
            }
            break;
        default:    //Surpress GCC warning of unhandled MessageTypes
            break;
    }


    if(packetHeader->messageType == MessageType::MODULE_CONFIG)
    {
        ConnPacketModule const * packet = (ConnPacketModule const *) packetHeader;

        if(packet->actionType == (u8)Module::ModuleConfigMessages::GET_MODULE_LIST)
        {
            SendModuleList(packet->header.sender, packet->requestHandle);

        }
        else if(packet->actionType == (u8)Module::ModuleConfigMessages::MODULE_LIST_V2)
        {
            logjson_partial("MODULE", "{\"nodeId\":%u,\"type\":\"module_list\",\"modules\":[", packet->header.sender);

            u16 moduleCount = (sendData->dataLength - SIZEOF_CONN_PACKET_MODULE).GetRaw() / sizeof(ModuleInformation);
            for(int i = 0; i < moduleCount; i++)
            {
                const ModuleInformation* info = (const ModuleInformation*)(packet->data + i * sizeof(ModuleInformation));

                if(i > 0){ logjson_partial("MODULE", ","); }
                logjson_partial("MODULE", "{\"id\":%s,\"version\":%u,\"active\":%u}", Utility::GetModuleIdString(info->moduleId).data(), info->moduleVersion, info->moduleActive);
            }
            logjson("MODULE", "]}" SEP);
        }
    }


    if(packetHeader->messageType == MessageType::MODULE_TRIGGER_ACTION){
        ConnPacketModule const * packet = (ConnPacketModule const *)packetHeader;

        //Check if our module is meant and we should trigger an action
        if(packet->moduleId == ModuleId::NODE){
            if (packet->actionType == (u8)NodeModuleTriggerActionMessages::GET_TIME) {
                u32 unixTimeStamp = GS->timeManager.GetUtcTime();
                TimeSyncState state;
                if (GS->timeManager.IsTimeCorrected()) {
                    state = TimeSyncState::CORRECTED;
                }
                else if (GS->timeManager.IsTimeSynced()) {
                    state = TimeSyncState::SYNCED;
                }
                else {
                    state = TimeSyncState::UNSYNCED;
                }
                GetTimeResponseMessage data{
                    unixTimeStamp,
                    (i16)GS->timeManager.GetOffset(),
                    state,
                    GS->timeManager.IsTimeMaster(),
                    0
                };

                SendModuleActionMessage(
                    MessageType::MODULE_ACTION_RESPONSE,
                    packetHeader->sender,
                    (u8)NodeModuleActionResponseMessages::GET_TIME_RESULT,
                    0,
                    (u8*)&data,
                    SIZEOF_GET_TIME_RESPONSE_MESSAGE,
                    false
                );
            }

            if(packet->actionType == (u8)NodeModuleTriggerActionMessages::SET_DISCOVERY){

                u8 ds = packet->data[0];

                if(ds == 0){
                    ChangeState(DiscoveryState::IDLE);
                } else {
                    ChangeState(DiscoveryState::HIGH);
                }

                SendModuleActionMessage(
                    MessageType::MODULE_ACTION_RESPONSE,
                    packetHeader->sender,
                    (u8)NodeModuleActionResponseMessages::SET_DISCOVERY_RESULT,
                    0,
                    nullptr,
                    0,
                    false
                );
            }

            if (packet->actionType == (u8)NodeModuleTriggerActionMessages::PING) {
                SendModuleActionMessage(
                    MessageType::MODULE_ACTION_RESPONSE,
                    packetHeader->sender,
                    (u8)NodeModuleActionResponseMessages::PING,
                    packet->requestHandle,
                    nullptr,
                    0,
                    false
                );
            }

            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::START_GENERATE_LOAD) {
                // 检查消息大小来判断是否包含 priority 字段
                const u8 payloadLength = sendData->dataLength.GetRaw() - SIZEOF_CONN_PACKET_MODULE;

                trace("DEBUG: Received START_GENERATE_LOAD, payloadLength=%u, sizeof(GenerateLoadMixedMessage)=%u" EOL, 
                    payloadLength, sizeof(GenerateLoadMixedMessage));

                // 檢查是否為混合交錯模式（使用特殊 requestHandle=0xFD）
                if (packet->requestHandle == 0xFD && payloadLength >= sizeof(GenerateLoadMixedMessage)) {
                    // 混合交錯模式
                    GenerateLoadMixedMessage const * message = (GenerateLoadMixedMessage const *)packet->data;
                    generateLoadTarget = message->target;
                    generateLoadPayloadSize = message->size;
                    generateLoadTimeBetweenMessagesDs = message->timeBetweenMessagesDs;

                     // 直接讀取參數（不需要解碼）
                    u8 multiplier = message->requestHandle;
                    u8 ratio = message->interleavingRatio;
                    if (multiplier == 0) multiplier = 1; // 防止除以 0
                    if (ratio == 0) ratio = 3; // 預設 3:1

                    // 設定混合模式參數
                    generateLoadMixedMode = true;
                    generateLoadWithPriorityFlag = true;
                    generateLoadHighTarget = message->highAmount * multiplier;  // 乘以 multiplier
                    generateLoadLowTarget = message->lowAmount * multiplier;    // 乘以 multiplier
                    generateLoadHighSent = 0;
                    generateLoadLowSent = 0;
                    generateLoadHighActualSent = 0;  // 重置實際發送計數（含重傳）
                    generateLoadLowActualSent = 0;   // 重置實際發送計數（含重傳）
                    generateLoadMixedCounter = 0;
                    generateLoadMessagesLeft = (message->highAmount + message->lowAmount) * multiplier;
                    generateLoadRequestHandle = 0;

                    GS->CollsndCount = 0;
                    GS->MultipleCount = 0;
                    GS->MultipleUnit = multiplier;

                    trace("DEBUG: gen_load_mixed - HIGH=%u, LOW=%u, ratio=%u:1, multiplier=%u, total=%u" EOL, 
                        message->highAmount, message->lowAmount, ratio, multiplier, generateLoadMessagesLeft);

                    logt("NODE", "Generating MIXED interleaved load. Target: %u size: %u HIGH: %u LOW: %u ratio: %u:1 multiplier: %u interval: %u",
                        message->target,
                        message->size,
                        message->highAmount,
                        message->lowAmount,
                        ratio,
                        multiplier,
                        message->timeBetweenMessagesDs);
                }
                else if (payloadLength >= sizeof(GenerateLoadWithPriorityMessage)) {
                    // 包含 priority 的新格式
                    trace("DEBUG: Using NEW format (with priority)" EOL);
                    GenerateLoadWithPriorityMessage const * message = (GenerateLoadWithPriorityMessage const *)packet->data;
                    generateLoadTarget = message->target;
                    generateLoadPayloadSize = message->size;
                    generateLoadMessagesLeft = message->amount * packet->requestHandle;
                    generateLoadTimeBetweenMessagesDs = message->timeBetweenMessagesDs;
                    generateLoadPriority = message->priority; // 保存 priority
                    generateLoadWithPriorityFlag = true; // 设置标志
                    generateLoadMixedMode = false; // 清除混合模式
                    generateLoadRequestHandle = 0;

                    GS->CollsndCount = 0;
                    GS->MultipleCount = 0;
                    GS->MultipleUnit = packet->requestHandle;

                    trace("DEBUG: gen_load_prio - MultipleUnit=%u, amount=%u, requestHandle=%u, priority=%u" EOL, 
                        GS->MultipleUnit, message->amount, packet->requestHandle, message->priority);

                    logt("NODE", "Generating load with priority. Target: %u size: %u amount: %u interval: %u priority: %u requestHandle: %u",
                        message->target,
                        message->size,
                        message->amount * packet->requestHandle,
                        message->timeBetweenMessagesDs,
                        message->priority,
                        packet->requestHandle);
                } else {
                    // 原始格式，没有 priority
                    trace("DEBUG: Using OLD format (without priority)" EOL);
                    GenerateLoadTriggerMessage const * message = (GenerateLoadTriggerMessage const *)packet->data;
                    generateLoadTarget = message->target;
                    generateLoadPayloadSize = message->size;
                    generateLoadMessagesLeft = message->amount * packet->requestHandle;
                    generateLoadTimeBetweenMessagesDs = message->timeBetweenMessagesDs;
                    generateLoadPriority = 3; // Default to LOW priority
                    generateLoadWithPriorityFlag = false; // 清除标志
                    generateLoadMixedMode = false; // 清除混合模式
                    generateLoadRequestHandle = 0;

                    GS->CollsndCount = 0;
                    GS->MultipleCount = 0;
                    GS->MultipleUnit = packet->requestHandle;
                    
                     // 初始化發送端計數器（用於後續 snd_prio 收集）
                    generateLoadHighSent = 0;
                    generateLoadLowSent = 0;
                    generateLoadHighActualSent = 0;  // 重置實際發送計數
                    generateLoadLowActualSent = 0;   // 重置實際發送計數

                    trace("DEBUG: multi_generate_load - MultipleUnit=%u, amount=%u, requestHandle=%u" EOL, 
                        GS->MultipleUnit, message->amount, packet->requestHandle);

                    logt("NODE", "Generating load. Target: %u size: %u amount: %u interval: %u requestHandle: %u",
                        message->target,
                        message->size,
                        message->amount * packet->requestHandle,
                        message->timeBetweenMessagesDs,
                        packet->requestHandle);
                }

                SendModuleActionMessage(
                    MessageType::MODULE_ACTION_RESPONSE,
                    packetHeader->sender,
                    (u8)NodeModuleActionResponseMessages::START_GENERATE_LOAD_RESULT,
                    0, // update packet->requestHandle
                    nullptr,
                    0,
                    false
                );
            }

            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::GENERATE_LOAD_CHUNK) {
                u8 const * payload = packet->data;
                bool payloadCorrect = true;
                const u8 payloadLength = sendData->dataLength.GetRaw() - SIZEOF_CONN_PACKET_MODULE;
                // 新增：检测 priority 标记
                u8 receivedPriority = 3; // 默认 LOW
                bool hasPriorityMarker = false;
                u32 startIdx = 0;

                if (payloadLength > 0 && (payload[0] & 0xF0) == generateLoadPriorityMarker) {
                    hasPriorityMarker = true;
                    receivedPriority = payload[0] & 0x0F;
                    startIdx = 1;
                }

                // 验证 payload
                for (u32 i = startIdx; i < payloadLength; i++)
                {
                    if (payload[i] != generateLoadMagicNumber)
                    {
                        payloadCorrect = false;
                    }
                }
                //new: calculate packet delay nonimportant
                u32 packetReceivedTime = GS->delaytimer;
                u32 packetDelay = 0;
                if (packetReceivedTime >= packet->timestamp)
                    packetDelay = packetReceivedTime - packet->timestamp;
                else
                    packetDelay = packet->timestamp - packetReceivedTime;

                avgDelay[packetHeader->sender - 1] += packetDelay;
                rcvCountArray[packetHeader->sender - 1] += 1;
                // GS->rcvCount += 1; // 累加全局接收计数

                // 新增：分别统计 high/low priority
                if (hasPriorityMarker) {
                    if (receivedPriority <= 1) { // HIGH or VITAL
                        avgDelayHighPrio[packetHeader->sender - 1] += packetDelay;
                        rcvCountHighPrio[packetHeader->sender - 1] += 1;
                    } else { // MEDIUM or LOW
                        avgDelayLowPrio[packetHeader->sender - 1] += packetDelay;
                        rcvCountLowPrio[packetHeader->sender - 1] += 1;
                    }
                }


                for (u32 i = 0; i < payloadLength; i++)
                {
                    if (payload[i] != generateLoadMagicNumber)
                    {
                        payloadCorrect = false;
                    }
                }

                if (payloadCorrect == true && configuration.nodeId == packetHeader->receiver && packetHeader->sender != 10)
                    GS->rcvCount += 1;

                if ((GS->rcvCount % 1000) == 0)
                {
                    // logjson("NODE", "{\"type\":\"generate_load_chunk\",\"nodeId\":%d,\"size\":%u,\"payloadCorrect\":%u,\"receivedTime\":%u, \"stamp\":%u, \"delay\":%u}" SEP, packetHeader->sender, (u32)payloadLength, (u32)payloadCorrect, packetReceivedTime, packet->timestamp, packetDelay);
                }
                // trace("node id : %d, generateTime : %u ms, sendTime : %u ms, receivedTime : %u ms, delay : %u ms," EOL, packetHeader->sender,packet->timestamp,packet->sendtime,packetReceivedTime,packetDelay);
            }
            //new collect data
            else if(packet->actionType == (u8)NodeModuleTriggerActionMessages::COLLECT_TRANSMIT_DATA)
            {
                        SendModuleActionMessage(
                            MessageType::MODULE_TRIGGER_ACTION,
                            packetHeader->sender,
                            (u8)NodeModuleTriggerActionMessages::TRANSMIT_DATA_CollsndCount,
                            GS->CollsndCount,
                            nullptr,
                            0,
                            false
                        );
                        SendModuleActionMessage(
                            MessageType::MODULE_TRIGGER_ACTION,
                            packetHeader->sender,
                            (u8)NodeModuleTriggerActionMessages::TRANSMIT_DATA_MultipleCount,
                            GS->MultipleCount,
                            nullptr,
                            0, 
                            false
                        );    
                        GS->CollsndCount=0;
                        GS->MultipleCount=0; 
                    
            }

            // 新增：收集混合模式統計
            else if(packet->actionType == (u8)NodeModuleTriggerActionMessages::COLLECT_MIXED_DATA)
            {
                 // 發送 HIGH priority 實際計數（含重傳）
                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    packetHeader->sender,
                    (u8)NodeModuleTriggerActionMessages::TRANSMIT_MIXED_HIGH_COUNT,
                    0,
                    (u8*)&generateLoadHighActualSent,
                    sizeof(generateLoadHighActualSent),
                    false
                );
                // 發送 LOW priority 計數
                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    packetHeader->sender,
                    (u8)NodeModuleTriggerActionMessages::TRANSMIT_MIXED_LOW_COUNT,
                    0,
                    (u8*)&generateLoadLowActualSent,
                    sizeof(generateLoadLowActualSent),
                    false
                );
            }
            // 接收 HIGH priority 計數
            else if(packet->actionType == (u8)NodeModuleTriggerActionMessages::TRANSMIT_MIXED_HIGH_COUNT)
            {
                u32 count = 0;
                if (sendData->dataLength.GetRaw() >= SIZEOF_CONN_PACKET_MODULE + sizeof(u32)) {
                    CheckedMemcpy(&count, packet->data, sizeof(u32));
                }
                if (packetHeader->sender > 0 && packetHeader->sender <= 100) {
                    sndCountHighPrio[packetHeader->sender - 1] = count;
                }
            }
            // 接收 LOW priority 計數
            else if(packet->actionType == (u8)NodeModuleTriggerActionMessages::TRANSMIT_MIXED_LOW_COUNT)
            {
                u32 count = 0;
                if (sendData->dataLength.GetRaw() >= SIZEOF_CONN_PACKET_MODULE + sizeof(u32)) {
                    CheckedMemcpy(&count, packet->data, sizeof(u32));
                }
                if (packetHeader->sender > 0 && packetHeader->sender <= 100) {
                    sndCountLowPrio[packetHeader->sender - 1] = count;
                }
            }

            //new collect data
            else if(packet->actionType == (u8)NodeModuleTriggerActionMessages::TRANSMIT_DATA_CollsndCount)
            {
                GS->CollsndCount+=(u32)packet->requestHandle;
                CollsndCountArray[packetHeader->sender-1]+=(u32)packet->requestHandle;
            }
            //new collect data
            else if(packet->actionType == (u8)NodeModuleTriggerActionMessages::TRANSMIT_DATA_MultipleCount)
            {
                 GenerateLoadTriggerMessage const * message = (GenerateLoadTriggerMessage const *)packet->data; //new
                GS->MultipleCount+=(u32)packet->requestHandle;
                MultipleCountArray[packetHeader->sender-1]+=(u32)packet->requestHandle;
                trace("GS->MultipleCount %u" EOL, GS->MultipleCount);
               

                
            }

            //new find_degree
            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::FIND_DEGREE)
            {
                TOTAL_NODE_NUM = 3;

                    /*初始化deg記憶體空間==-1*/
                if (init == -1) {


                    for (int i = 0; i <= TOTAL_NODE_NUM; i++) {
                        deg[i] = -1;
                    }

                    init = 1;
                 }

                    /*設置deg*/
                deg[packetHeader->sender]= ((u32)packet->requestHandle);
                trace("Node: %d  deg: %d\n" EOL, packetHeader->sender, deg[packetHeader->sender]);//test
                if (packetHeader->receiver != root) {
                    deg[packetHeader->receiver] = ((u32)packet->requestHandle) + 1;
                    GS->node.parent = packetHeader->sender;
                }
                else GS->node.parent = 255; // 如顯示255;

                trace("Node: %d  deg: %d\n" EOL, packetHeader->receiver, deg[packetHeader->receiver]);
                
                 BaseConnections conn = GS->cm.GetBaseConnections(ConnectionDirection::INVALID);
                 for (u8 i = 0; i < conn.count; i++)
                  {
                  if (conn.handles[i]) {
                    if (GS->node.parent != conn.handles[i].GetPartnerId()) {
                        deg[conn.handles[i].GetPartnerId()] = deg[packetHeader->receiver] + 1;
                       SendModuleActionMessage(
                       MessageType::MODULE_TRIGGER_ACTION, //MessageType messageType
                       conn.handles[i].GetPartnerId(),     //NodeId toNode
                       (u8)NodeModuleTriggerActionMessages::FIND_DEGREE,                                 //u8 actionType
                       deg[packetHeader->receiver],                                  //u8 requestHandle 將目前deg的值傳給兒子
                       nullptr,                            //const u8* additionalData
                       0,                                  //u16 additionalDataSize
                       false                              //bool reliable
                           );
                       }
                     }
                  }
            }
            //new init_state
            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::INIT_STATE)
            {
                BaseConnections conn = GS->cm.GetBaseConnections(ConnectionDirection::INVALID);
                for (u8 i = 0; i < conn.count; i++)
                {
                    if (conn.handles[i]) {
                        if (GS->node.parent != conn.handles[i].GetPartnerId()) {
                            SendModuleActionMessage(
                                MessageType::MODULE_TRIGGER_ACTION, //MessageType messageType
                                conn.handles[i].GetPartnerId(),     //NodeId toNode
                                (u8)NodeModuleTriggerActionMessages::INIT_STATE,                                 //u8 actionType
                                0,                                  //u8 requestHandle 
                                nullptr,                            //const u8* additionalData
                                0,                                  //u16 additionalDataSize
                                false                              //bool reliable
                            );
                        }
                        else if (deg[packetHeader->receiver] % 2 != 0) {
                            trace("禁用\n");//test
                            SendModuleActionMessage(
                                MessageType::MODULE_TRIGGER_ACTION, //MessageType messageType
                                conn.handles[i].GetPartnerId(),     //NodeId toNode
                                (u8)NodeModuleTriggerActionMessages::DISABLED_CONN,                              //u8 actionType
                                0,                                 //u8 requestHandle 
                                nullptr,                            //const u8* additionalData
                                0,                                  //u16 additionalDataSize
                                false                              //bool reliable
                            );
                            conn.handles[i].Disabled();
                            counta++; //測試有沒有正確執行用的
                            trace("當前node為%d  目標node為 %d 的conn已設置%u\n\n", packetHeader->receiver, conn.handles[i].GetPartnerId(), (u8)conn.handles[i].GetConnectionState()); // test
                        }
                    }
                }
                }
            
            //new disable_conn
            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::DISABLED_CONN)
            {   
                BaseConnections conn = GS->cm.GetBaseConnections(ConnectionDirection::INVALID);
                for (u8 i = 0; i < conn.count; i++)
                {
                    if (conn.handles[i]) {
                        if (packetHeader->sender == conn.handles[i].GetPartnerId()) {
                            conn.handles[i].Disabled();
                            counta++; //test
                            trace("當前node為%d  目標node為 %d 的conn已設置%u\n\n", packetHeader->receiver, conn.handles[i].GetPartnerId(), (u8)conn.handles[i].GetConnectionState()); //test
                        }

                    }
                }
            }
            //new set_flag 切換啟用禁用 (當網路完成初始化)
            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::SET_FLAG)
            {   flag=1;
                BaseConnections conn = GS->cm.GetBaseConnections(ConnectionDirection::INVALID);
                for (u8 i = 0; i < conn.count; i++)
                {
                    if (conn.handles[i]) {
                        if (GS->node.parent != conn.handles[i].GetPartnerId()) {
                           SendModuleActionMessage(
                        MessageType::MODULE_TRIGGER_ACTION, //MessageType messageType
                        conn.handles[i].GetPartnerId(),     //NodeId toNode
                        (u8)NodeModuleTriggerActionMessages::SET_FLAG,                                 //u8 actionType
                        deg[packetHeader->receiver],                                  //u8 requestHandle 將目前deg的值傳給兒子
                        nullptr,                            //const u8* additionalData
                        0,                                  //u16 additionalDataSize
                        false                              //bool reliable
                        );
                    }
                }
                }
            }

            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::SET_UNIT)
            {
                 GS->MultipleUnit=packet->requestHandle;
            }
            

            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::RESET_NODE)
            {
                NodeModuleResetMessage const * message = (NodeModuleResetMessage const *)packet->data;
                logt("NODE", "Scheduled reboot in %u seconds", message->resetSeconds);
                Reboot(message->resetSeconds*10, RebootReason::REMOTE_RESET);
            }
            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::EMERGENCY_DISCONNECT)
            {
                EmergencyDisconnectResponseMessage response;
                CheckedMemset(&response, 0, sizeof(response));

                if (GS->cm.freeMeshOutConnections == 0)
                {
                    MeshConnectionHandle connToDisconnect;

                    //We want to disconnect connections with a low number of connected nodes
                    //Therefore we give these a higher chance to get disconnected
                    u16 rnd = Utility::GetRandomInteger();
                    u32 sum = 0;

                    MeshConnections conns = GS->cm.GetMeshConnections(ConnectionDirection::DIRECTION_OUT);

                    u16 handshakedConnections = 0;
                    for (u32 i = 0; i < conns.count; i++) {
                        if (conns.handles[i].IsHandshakeDone()) handshakedConnections++;
                    }

                    //We try to find a connection that we should disconnect based on probability.
                    //Connections with less connectedClusterSize should be preferredly disconnected
                    for (u32 i = 0; i < conns.count; i++) {
                        MeshConnectionHandle conn = conns.handles[i];
                        if (!conn.IsHandshakeDone()) continue;

                        //The probability from 0 to UINT16_MAX that this connection will be removed
                        //Because our node counts against the clusterSize but is not included in the connectedClusterSizes, we substract 1
                        //We also check that we do not have a divide by 0 exception
                        u32 removalProbability = (handshakedConnections <= 1 || clusterSize <= 1) ? 1 : ((clusterSize - 1) - conn.GetConnectedClusterSize()) * UINT16_MAX / ((handshakedConnections - 1) * (clusterSize - 1));

                        sum += removalProbability;

                        //TODO: Maybe we do not want linear probablility but more sth. exponential?

                        if (sum > rnd) {
                            connToDisconnect = conn;
                            break;
                        }
                    }

                    if (connToDisconnect) {
                        logt("WARNING", "Emergency disconnect from %u", connToDisconnect.GetPartnerId());
                        response.code = EmergencyDisconnectErrorCode::SUCCESS;

                        connToDisconnect.DisconnectAndRemove(AppDisconnectReason::EMERGENCY_DISCONNECT);
                        GS->logger.LogCustomError(CustomErrorTypes::INFO_EMERGENCY_DISCONNECT_SUCCESSFUL, 0);

                        //TODO: Blacklist other node for a short time
                    }
                    else {
                        response.code = EmergencyDisconnectErrorCode::CANT_DISCONNECT_ANYBODY;
                        GS->logger.LogCustomCount(CustomErrorTypes::COUNT_EMERGENCY_CONNECTION_CANT_DISCONNECT_ANYBODY);
                        logt("WARNING", "WOULD DISCONNECT NOBODY");
                    }
                }
                else
                {
                    response.code = EmergencyDisconnectErrorCode::NOT_ALL_CONNECTIONS_USED_UP;
                }

                SendModuleActionMessage(
                    MessageType::MODULE_ACTION_RESPONSE,
                    packetHeader->sender,
                    (u8)NodeModuleActionResponseMessages::EMERGENCY_DISCONNECT_RESULT,
                    0,
                    (u8*)&response,
                    sizeof(response),
                    false
                );
            }
            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::SET_PREFERRED_CONNECTIONS)
            {
                PreferredConnectionMessage const * message = (PreferredConnectionMessage const *)packet->data;
                if (message->amountOfPreferredPartnerIds > Conf::MAX_AMOUNT_PREFERRED_PARTNER_IDS)
                {
                    //Packet seems to be malformed!
                    SIMEXCEPTION(IllegalArgumentException); //LCOV_EXCL_LINE assertion
                    return;
                }

                GS->config.configuration.amountOfPreferredPartnerIds = message->amountOfPreferredPartnerIds;
                GS->config.configuration.preferredConnectionMode = message->preferredConnectionMode;
                for (u16 i = 0; i < message->amountOfPreferredPartnerIds; i++) {
                    GS->config.configuration.preferredPartnerIds[i] = message->preferredPartnerIds[i];
                }

                GS->config.SaveConfigToFlash(nullptr, 0, nullptr, 0);

                //Reboot is the safest way to make sure that we reevaluate all the possible connection partners.
                Reboot(SEC_TO_DS(10), RebootReason::PREFERRED_CONNECTIONS);

                SendModuleActionMessage(
                    MessageType::MODULE_ACTION_RESPONSE,
                    packetHeader->sender,
                    (u8)NodeModuleActionResponseMessages::SET_PREFERRED_CONNECTIONS_RESULT,
                    0,
                    nullptr,
                    0,
                    false
                );
            }
            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::SET_ENROLLED_NODES)
            {
                const u16 enrolledNodes = (u16)(((SetEnrolledNodesMessage const *)&packet->data)->enrolledNodes);

                SetEnrolledNodes(enrolledNodes, packet->header.sender);
                if (GS->node.configuration.numberOfEnrolledDevices == 0)
                {
                    ChangeState(DiscoveryState::HIGH);
                }
                else if (GS->node.configuration.numberOfEnrolledDevices == GS->node.GetClusterSize())
                {
                    ChangeState(DiscoveryState::IDLE);
                }
                else if (GS->node.configuration.numberOfEnrolledDevices < GS->node.GetClusterSize())
                {
                    //If current cluster size is bigger than requested number of enrolled devices we want to wait a bit
                    //and then check if current configuration is valid.
                    clusterSizeChangeHandled = false;
                    clusterSizeTransitionTimeoutDs = SEC_TO_DS((u32)Conf::GetInstance().clusterSizeDiscoveryChangeDelaySec);
                }
                else if (GS->node.configuration.numberOfEnrolledDevices > GS->node.GetClusterSize())
                {
                    //We want high discovery state when number of enrolled devices is higher then cluster size as
                    //nodes are probably nearby and will soon join network
                    ChangeState(DiscoveryState::HIGH);
                }
                
                SetEnrolledNodesResponseMessage responseMessage;
                responseMessage.enrolledNodes = GS->node.configuration.numberOfEnrolledDevices;
                SendModuleActionMessage(
                    MessageType::MODULE_ACTION_RESPONSE,
                    packetHeader->sender,
                    (u8)NodeModuleActionResponseMessages::SET_ENROLLED_NODES_RESULT,
                    0,
                    (u8*)(&responseMessage),
                    sizeof(responseMessage),
                    false
                );
            }
            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::ADD_DYNAMIC_GROUP)
            {
                MessageLength messageBytes = (sendData->dataLength - SIZEOF_CONN_PACKET_MODULE).GetRaw();
                if (messageBytes < sizeof(NodeId))
                {
                    SIMEXCEPTION(IllegalStateException);
                    return;
                }
                const NodeId group = ((AddOrRemoveDynamicGroupMessage const*)&packet->data)->id;
                if (group < NODE_ID_DYNAMIC_GROUP_BASE || group >= NODE_ID_DYNAMIC_GROUP_BASE + NODE_ID_DYNAMIC_GROUP_BASE_SIZE)
                {
                    SendGroupResponse(packetHeader->sender, NodeModuleActionResponseMessages::ADD_DYNAMIC_GROUP, packet->requestHandle, group, AddDynamicGroupResponseMessageCode::OUT_OF_RANGE);
                    return;
                }
                else
                {
                    // Check if we are already in that group.
                    for (u32 i = 0; i < MAX_AMOUNT_OF_DYNAMIC_GROUP_IDS; i++)
                    {
                        if (configuration.dynamicGroupIds[i] == group)
                        {
                            // Immediately return success.
                            SendGroupResponse(packetHeader->sender, NodeModuleActionResponseMessages::ADD_DYNAMIC_GROUP, packet->requestHandle, group, AddDynamicGroupResponseMessageCode::SUCCESS);
                            return;
                        }
                    }

                    // Search for the first free spot
                    for (u32 i = 0; i < MAX_AMOUNT_OF_DYNAMIC_GROUP_IDS; i++)
                    {
                        if (!configuration.dynamicGroupIds[i])
                        {
                            configuration.dynamicGroupIds[i] = group;
                            SaveRecordStorageDynamicGroup(packetHeader->sender, NodeModuleActionResponseMessages::ADD_DYNAMIC_GROUP, packet->requestHandle, group);
                            return;
                        }
                    }

                    SendGroupResponse(packetHeader->sender, NodeModuleActionResponseMessages::ADD_DYNAMIC_GROUP, packet->requestHandle, group, AddDynamicGroupResponseMessageCode::NO_GROUPS_LEFT);
                }
            }
            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::REMOVE_DYNAMIC_GROUP)
            {
                const NodeId group = ((AddOrRemoveDynamicGroupMessage const*)&packet->data)->id;

                bool changed = false;
                for (u32 i = 0; i < MAX_AMOUNT_OF_DYNAMIC_GROUP_IDS; i++)
                {
                    if (configuration.dynamicGroupIds[i] == group)
                    {
                        configuration.dynamicGroupIds[i] = 0;
                        changed = true;
                    }
                }
                if (changed)
                {
                    SaveRecordStorageDynamicGroup(packetHeader->sender, NodeModuleActionResponseMessages::REMOVE_DYNAMIC_GROUP, packet->requestHandle, group);
                }
                else
                {
                    SendGroupResponse(packetHeader->sender, NodeModuleActionResponseMessages::REMOVE_DYNAMIC_GROUP, packet->requestHandle, group, AddDynamicGroupResponseMessageCode::SUCCESS);
                }
            }
            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::CLEAR_DYNAMIC_GROUPS)
            {
                CheckedMemset(configuration.dynamicGroupIds, 0x00, sizeof(configuration.dynamicGroupIds));
                SaveRecordStorageDynamicGroup(packetHeader->sender, NodeModuleActionResponseMessages::CLEAR_DYNAMIC_GROUPS, packet->requestHandle, 0);
            }
            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::GET_DYNAMIC_GROUPS)
            {
                // See: GetDynamicGroupsResponseMessage
                NodeId ids[MAX_AMOUNT_OF_DYNAMIC_GROUP_IDS];
                CheckedMemset(ids, 0, sizeof(ids));
                u32 writeHead = 0;
                for (u32 i = 0; i < MAX_AMOUNT_OF_DYNAMIC_GROUP_IDS; i++)
                {
                    if (configuration.dynamicGroupIds[i] != 0)
                    {
                        ids[writeHead] = configuration.dynamicGroupIds[i];
                        writeHead++;
                    }
                }

                SendModuleActionMessage(
                    MessageType::MODULE_ACTION_RESPONSE,
                    packetHeader->sender,
                    (u8)NodeModuleActionResponseMessages::GET_DYNAMIC_GROUPS,
                    packet->requestHandle,
                    (u8*)ids,
                    writeHead * sizeof(NodeId),
                    false
                );
            }

            //新增加設置scan interval
            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::SET_SCAN_INTERVAL)
            {
                if (sendData->dataLength >= (SIZEOF_CONN_PACKET_MODULE + sizeof(UpdateConnIntervalMessage)))
                {
                    UpdateConnIntervalMessage const * message = (UpdateConnIntervalMessage const *)packet->data;
                    u16 newIntervalMs = message->newIntervalMs;
                    logt("NODE", "Setting scan interval to %u ms.", newIntervalMs);

                    u16 scanIntervalUnits = MSEC_TO_UNITS(newIntervalMs, CONFIG_UNIT_0_625_MS);
                    RamConfig->meshScanIntervalHigh = scanIntervalUnits;
                    RamConfig->meshScanIntervalLow = scanIntervalUnits;

                    ChangeState(currentDiscoveryState); // Apply new scan settings

                    SendModuleActionMessage(
                        MessageType::MODULE_ACTION_RESPONSE,
                        packetHeader->sender,
                        (u8)NodeModuleActionResponseMessages::SET_SCAN_INTERVAL_RESULT,
                        packet->requestHandle, nullptr, 0, false);
                }
            }

            //新加入調整connection interval
            else if (packet->actionType == (u8)NodeModuleTriggerActionMessages::SET_CONN_INTERVAL)
            {
                // Support both old and new message format for compatibility
                NodeId targetNodeId = 0;
                u16 newIntervalMs = 0;

                // Define the new message structure locally for this handler
                struct UpdateConnIntervalMessageWithTarget {
                    u16 newIntervalMs;
                    NodeId targetNodeId;
                };

                if (sendData->dataLength >= (SIZEOF_CONN_PACKET_MODULE + sizeof(UpdateConnIntervalMessageWithTarget))) {
                    // New format: { newIntervalMs, targetNodeId }
                    UpdateConnIntervalMessageWithTarget const * message = (UpdateConnIntervalMessageWithTarget const *)packet->data;
                    newIntervalMs = message->newIntervalMs;
                    targetNodeId = message->targetNodeId;
                } else if (sendData->dataLength >= (SIZEOF_CONN_PACKET_MODULE + sizeof(u16))) {
                    // Old format: { newIntervalMs }
                    UpdateConnIntervalMessage const * message = (UpdateConnIntervalMessage const *)packet->data;
                    newIntervalMs = message->newIntervalMs;
                } else {
                    // Not enough data
                    return;
                }

                if (targetNodeId != 0) {
                    // A specific peer is targeted
                    logt("NODE", "Setting connection interval for peer %u to %u ms.", targetNodeId, newIntervalMs);

                    bool found = false;
                    MeshConnections conns = GS->cm.GetMeshConnections(ConnectionDirection::INVALID);
                    for (u32 i = 0; i < conns.count; i++) {
                        if (conns.handles[i].GetPartnerId() == targetNodeId) {
                            // Directly call the UpdateConnectionInterval method on the Node class
                            UpdateConnectionInterval(conns.handles[i].GetConnection()->connectionHandle, newIntervalMs);(conns.handles[i].GetConnection()->connectionHandle, newIntervalMs);
                            found = true;
                            break;
                        }
                    }

                    if (!found) {
                        logt("NODE", "Target peer %u not found or not a mesh connection.", targetNodeId);
                    }
                } else {
                    // No specific peer, update all connections (original behavior)
                    logt("NODE", "Setting connection interval to %u ms and scheduling updates for all connections.", newIntervalMs);

                    u16 connIntervalUnits = MSEC_TO_UNITS(newIntervalMs, CONFIG_UNIT_1_25_MS);
                    RamConfig->meshMinConnectionInterval = connIntervalUnits;
                    RamConfig->meshMaxConnectionInterval = connIntervalUnits;

                    // Kick off the state machine to update existing connections
                    connUpdateIntervalMs = newIntervalMs;
                    connUpdateIndex = 0;
                    nextConnUpdateAllowedTimeDs = GS->appTimerDs;
                }

                SendModuleActionMessage(
                    MessageType::MODULE_ACTION_RESPONSE,
                    packetHeader->sender,
                    (u8)NodeModuleActionResponseMessages::SET_CONN_INTERVAL_RESULT,
                    packet->requestHandle, nullptr, 0, false);
            }
        }
    }

    if(packetHeader->messageType == MessageType::MODULE_ACTION_RESPONSE){
        ConnPacketModule const * packet = (ConnPacketModule const *)packetHeader;
        //Check if our module is meant and we should trigger an action
        if(packet->moduleId == ModuleId::NODE){
            if (packet->actionType == (u8)NodeModuleActionResponseMessages::GET_TIME_RESULT) {
                GetTimeResponseMessage const * message = (GetTimeResponseMessage const *)(packet->data);

                logjson("NODE", "{\"type\":\"get_time_result\",\"nodeId\":%d,\"module\":%u,\"syncState\":%u,\"time\":%u,\"offset\":%u,\"master\":%u}" SEP,
                    packetHeader->sender,
                    (u32)ModuleId::NODE,
                    (u32)message->timeSyncState,
                    message->unixTimeStamp,
                    message->offset,
                    message->isTimeMaster);

                //Now, for convenience, we also log the time in a more human readable format
                char timestring[100];
                TimeManager::ConvertTimeToString(message->unixTimeStamp, message->offset, 0, timestring, sizeof(timestring));
                logt("NODE", R"(Node %u reported: %s, timeSyncState: %u, isTimeMaster: %s)", packetHeader->sender, timestring, (u32)message->timeSyncState, message->isTimeMaster ? "true" : "false");
            }
            else if (packet->actionType == (u8)NodeModuleActionResponseMessages::SET_DISCOVERY_RESULT)
            {
                logjson("NODE", "{\"type\":\"set_discovery_result\",\"nodeId\":%d,\"module\":%u}" SEP, packetHeader->sender, (u32)ModuleId::NODE);
            }
            else if (packet->actionType == (u8)NodeModuleActionResponseMessages::PING)
            {
                logjson("NODE", "{\"type\":\"ping\",\"nodeId\":%d,\"module\":%u,\"requestHandle\":%u}" SEP, packetHeader->sender, (u32)ModuleId::NODE, packet->requestHandle);
            }
            else if (packet->actionType == (u8)NodeModuleActionResponseMessages::START_GENERATE_LOAD_RESULT)
            {
                logjson("NODE", "{\"type\":\"start_generate_load_result\",\"nodeId\":%d,\"requestHandle\":%u}" SEP, packetHeader->sender, packet->requestHandle);
            }
            else if (packet->actionType == (u8)NodeModuleActionResponseMessages::EMERGENCY_DISCONNECT_RESULT)
            {
                EmergencyDisconnectResponseMessage const * msg = (EmergencyDisconnectResponseMessage const *)packet->data;
                if (msg->code == EmergencyDisconnectErrorCode::SUCCESS || msg->code == EmergencyDisconnectErrorCode::NOT_ALL_CONNECTIONS_USED_UP)
                {
                    //All fine, we are now able to connect to the partner via a MeshConnection
                }
                else if (msg->code == EmergencyDisconnectErrorCode::CANT_DISCONNECT_ANYBODY)
                {
                    GS->logger.LogCustomError(CustomErrorTypes::WARN_EMERGENCY_DISCONNECT_PARTNER_COULDNT_DISCONNECT_ANYBODY, 0);
                }
                ResetEmergencyDisconnect();
            }
            else if (packet->actionType == (u8)NodeModuleActionResponseMessages::SET_PREFERRED_CONNECTIONS_RESULT)
            {
                logjson("NODE", "{\"type\":\"set_preferred_connections_result\",\"nodeId\":%d,\"module\":%u}" SEP, packetHeader->sender, (u32)ModuleId::NODE);
            }
            else if (packet->actionType == (u8)NodeModuleActionResponseMessages::SET_ENROLLED_NODES_RESULT)
            {
                const u16 enrolledNodes = (u16)(((SetEnrolledNodesResponseMessage const *)&packet->data)->enrolledNodes);
                logjson("NODE", "{\"type\":\"set_enrolled_nodes\",\"nodeId\":%d,\"module\":%d,\"enrolled_nodes\":%u}" SEP, packetHeader->sender, (u32)ModuleId::NODE, enrolledNodes);
                GS->cm.SetEnrolledNodesReplyReceived(packet->header.sender, enrolledNodes);
            }
            else if (packet->actionType == (u8)NodeModuleActionResponseMessages::ADD_DYNAMIC_GROUP)
            {
                DynamicGroupResponseMessage const* message = (DynamicGroupResponseMessage const*)(packet->data);
                logjson("NODE", "{\"type\":\"add_group_result\",\"nodeId\":%d,\"module\":%u,\"group\":%u,\"code\":%u}" SEP,
                    packetHeader->sender,
                    (u32)ModuleId::NODE,
                    (u32)message->id,
                    (u32)message->code);
            }
            else if (packet->actionType == (u8)NodeModuleActionResponseMessages::REMOVE_DYNAMIC_GROUP)
            {
                DynamicGroupResponseMessage const* message = (DynamicGroupResponseMessage const*)(packet->data);
                logjson("NODE", "{\"type\":\"remove_group_result\",\"nodeId\":%d,\"module\":%u,\"group\":%u,\"code\":%u}" SEP,
                    packetHeader->sender,
                    (u32)ModuleId::NODE,
                    (u32)message->id,
                    (u32)message->code);
            }
            else if (packet->actionType == (u8)NodeModuleActionResponseMessages::CLEAR_DYNAMIC_GROUPS)
            {
                DynamicGroupResponseMessage const* message = (DynamicGroupResponseMessage const*)(packet->data);
                logjson("NODE", "{\"type\":\"clear_groups_result\",\"nodeId\":%d,\"module\":%u,\"group\":%u,\"code\":%u}" SEP,
                    packetHeader->sender,
                    (u32)ModuleId::NODE,
                    (u32)message->id,
                    (u32)message->code);
            }
            else if (packet->actionType == (u8)NodeModuleActionResponseMessages::GET_DYNAMIC_GROUPS)
            {
                GetDynamicGroupsResponseMessage const* message = (GetDynamicGroupsResponseMessage const*)(packet->data);
                logjson_partial("NODE", "{\"type\":\"get_groups_result\",\"nodeId\":%d,\"module\":%u,\"groups\":[",
                    packetHeader->sender,
                    (u32)ModuleId::NODE);
                u16 groupCount = (sendData->dataLength - SIZEOF_CONN_PACKET_MODULE).GetRaw() / sizeof(NodeId);
                for (u32 i = 0; i < groupCount; i++)
                {
                    logjson_partial("NODE", "%d", message->ids[i]);
                    if (i < (u32)(groupCount - 1))
                    {
                        logjson_partial("NODE", ",");
                    }
                }
                logjson("NODE", "]}" SEP);
            }
            //新加入設置scan interval
            else if (packet->actionType == (u8)NodeModuleActionResponseMessages::SET_SCAN_INTERVAL_RESULT)
            {
                logjson("NODE", "{\"type\":\"set_scan_interval_result\",\"nodeId\":%d,\"module\":%u,\"requestHandle\":%u}" SEP, packetHeader->sender, (u32)ModuleId::NODE, packet->requestHandle);
            }
            //新加入調整connection interval
            else if (packet->actionType == (u8)NodeModuleActionResponseMessages::SET_CONN_INTERVAL_RESULT)
            {
                logjson("NODE", "{\"type\":\"set_conn_interval_result\",\"nodeId\":%d,\"module\":%u,\"requestHandle\":%u}" SEP, packetHeader->sender, (u32)ModuleId::NODE, packet->requestHandle);
            }
        }
    }

    if (packetHeader->messageType == MessageType::TIME_SYNC) {
        TimeSyncHeader const * packet = (TimeSyncHeader const *)packetHeader;
        if (packet->type == TimeSyncType::INITIAL)
        {
            TimeSyncInitial const * packet = (TimeSyncInitial const *)packetHeader;
            logt("TSYNC", "Received initial! NodeId: %u, Partner: %u", (u32)GS->node.configuration.nodeId, (u32)packet->header.header.sender);
            GS->timeManager.SetTime(*packet);

            TimeSyncInitialReply reply;
            CheckedMemset(&reply, 0, sizeof(TimeSyncInitialReply));
            reply.header.header.messageType = MessageType::TIME_SYNC;
            reply.header.header.receiver = packet->header.header.sender;
            reply.header.header.sender = packet->header.header.receiver;
            reply.header.type = TimeSyncType::INITIAL_REPLY;

            GS->cm.SendMeshMessage(
                (u8*)&reply,
                sizeof(TimeSyncInitialReply));
        }
        if (packet->type == TimeSyncType::INITIAL_REPLY)
        {
            TimeSyncInitialReply const * packet = (TimeSyncInitialReply const *)packetHeader;
            logt("TSYNC", "Received initial reply! NodeId: %u, Partner: %u", (u32)GS->node.configuration.nodeId, (u32)packet->header.header.sender);
            GS->cm.TimeSyncInitialReplyReceivedHandler(*packet);
        }
        if (packet->type == TimeSyncType::CORRECTION)
        {
            TimeSyncCorrection const * packet = (TimeSyncCorrection const *)packetHeader;
            logt("TSYNC", "Received correction! NodeId: %u, Partner: %u", (u32)GS->node.configuration.nodeId, (u32)packet->header.header.sender);
            GS->timeManager.AddCorrection(packet->correctionTicks);

            TimeSyncCorrectionReply reply;
            CheckedMemset(&reply, 0, sizeof(TimeSyncCorrectionReply));
            reply.header.header.messageType = MessageType::TIME_SYNC;
            reply.header.header.receiver = packet->header.header.sender;
            reply.header.header.sender = packet->header.header.receiver;
            reply.header.type = TimeSyncType::CORRECTION_REPLY;

            GS->cm.SendMeshMessage(
                (u8*)&reply,
                sizeof(TimeSyncCorrectionReply));
        }
        if (packet->type == TimeSyncType::CORRECTION_REPLY)
        {
            TimeSyncCorrectionReply const * packet = (TimeSyncCorrectionReply const *)packetHeader;
            logt("TSYNC", "Received correction reply! NodeId: %u, Partner: %u", (u32)GS->node.configuration.nodeId, (u32)packet->header.header.sender);
            GS->cm.TimeSyncCorrectionReplyReceivedHandler(*packet);
        }
        if (packet->type == TimeSyncType::INTER_NETWORK)
        {
            TimeSyncInterNetwork const* packet = (TimeSyncInterNetwork const*)packetHeader;
            if (GET_DEVICE_TYPE() == DeviceType::ASSET || GS->timeManager.IsTimeSynced() == false)
            {
                GS->timeManager.SetTime(*packet);
            }
        }
    }

    if (packetHeader->messageType == MessageType::MODULE_RAW_DATA) {
        RawDataHeader const* packet = (RawDataHeader const*)packetHeader;
        RawDataHeaderVendor const* packetVendor = (RawDataHeaderVendor const*)packetHeader;

        NodeId senderId = 0;
        ModuleIdWrapper moduleId = 0;
        u8 requestHandle = 0;
        RawDataActionType actionType = RawDataActionType::START;

        const u8* payloadPtr = nullptr;
        MessageLength payloadLength;

        if (!Utility::IsVendorModuleId(packet->moduleId)) {
            senderId = packet->connHeader.sender;
            moduleId = Utility::GetWrappedModuleId(packet->moduleId);
            requestHandle = packet->requestHandle;
            actionType = packet->actionType;
            payloadPtr = ((const u8*)packet) + sizeof(RawDataHeader);
            payloadLength = sendData->dataLength - sizeof(RawDataHeader);
        }
        else {
            senderId = packetVendor->connHeader.sender;
            moduleId = packetVendor->moduleId;
            requestHandle = packetVendor->requestHandle;
            actionType = packetVendor->actionType;
            payloadPtr = ((const u8*)packet) + sizeof(RawDataHeaderVendor);
            payloadLength = sendData->dataLength - sizeof(RawDataHeaderVendor);
        }

        if (actionType == RawDataActionType::START && payloadLength >= sizeof(RawDataStartPayload))
        {
            const RawDataStartPayload* packet = (const RawDataStartPayload*)payloadPtr;

            char metadataString[250] = {};
            Logger::ConvertBufferToBase64String(packet->metadata, payloadLength - SIZEOF_RAW_DATA_START_PAYLOAD, metadataString, sizeof(metadataString));

            if (strlen(metadataString) > 0) {
                logjson("NODE",
                    "{"
                        "\"nodeId\":%u,"
                        "\"type\":\"raw_data_start\","
                        "\"module\":%s,"
                        "\"numChunks\":%u,"
                        "\"protocol\":%u,"
                        "\"fmKeyId\":%u,"
                        "\"requestHandle\":%u,"
                        "\"metadata\":\"%s\""
                    "}" SEP,
                    senderId,
                    Utility::GetModuleIdString(moduleId).data(),
                    packet->numChunks,
                    packet->protocolId,
                    packet->fmKeyId,
                    requestHandle,
                    metadataString
                );
            } else {
                logjson("NODE",
                    "{"
                        "\"nodeId\":%u,"
                        "\"type\":\"raw_data_start\","
                        "\"module\":%s,"
                        "\"numChunks\":%u,"
                        "\"protocol\":%u,"
                        "\"fmKeyId\":%u,"
                        "\"requestHandle\":%u"
                    "}" SEP,
                    senderId,
                    Utility::GetModuleIdString(moduleId).data(),
                    packet->numChunks,
                    packet->protocolId,
                    packet->fmKeyId,
                    requestHandle
                );
            }

        }
        else if (actionType == RawDataActionType::START_RECEIVED)
        {
            char metadataString[250];
            Logger::ConvertBufferToBase64String(payloadPtr, payloadLength, metadataString, sizeof(metadataString));

            if (strlen(metadataString) > 0) {
                logjson("NODE",
                    "{"
                        "\"nodeId\":%u,"
                        "\"type\":\"raw_data_start_received\","
                        "\"module\":%s,"
                        "\"requestHandle\":%u,"
                        "\"metadata\":\"%s\""
                    "}" SEP,
                    senderId,
                    Utility::GetModuleIdString(moduleId).data(),
                    requestHandle,
                    metadataString
                );
            } else {
                logjson("NODE",
                    "{"
                        "\"nodeId\":%u,"
                        "\"type\":\"raw_data_start_received\","
                        "\"module\":%s,"
                        "\"requestHandle\":%u"
                    "}" SEP,
                    senderId,
                    Utility::GetModuleIdString(moduleId).data(),
                    requestHandle
                );
            }
        }
        else if (actionType == RawDataActionType::ERROR_T && payloadLength >= sizeof(RawDataErrorPayload))
        {
            const RawDataErrorPayload* packet = (const RawDataErrorPayload*)payloadPtr;

            logjson("NODE",
                "{"
                    "\"nodeId\":%u,"
                    "\"type\":\"raw_data_error\","
                    "\"module\":%s,"
                    "\"error\":%u,"
                    "\"destination\":%u,"
                    "\"requestHandle\":%u"
                "}" SEP,
                senderId,
                Utility::GetModuleIdString(moduleId).data(),
                (u32)packet->error,
                (u32)packet->destination,
                requestHandle
            );
        }
        else if (actionType == RawDataActionType::CHUNK && payloadLength >= SIZEOF_RAW_DATA_CHUNK_PAYLOAD)
        {
            const RawDataChunkPayload* packet = (const RawDataChunkPayload*)payloadPtr;

            char payloadString[250];
            Logger::ConvertBufferToBase64String(packet->payload, payloadLength - SIZEOF_RAW_DATA_CHUNK_PAYLOAD, payloadString, sizeof(payloadString));

            logjson("NODE",
                "{"
                    "\"nodeId\":%u,"
                    "\"type\":\"raw_data_chunk\","
                    "\"module\":%s,"
                    "\"chunkId\":%u,"
                    "\"payload\":\"%s\","
                    "\"requestHandle\":%u"
                "}" SEP,
                senderId,
                Utility::GetModuleIdString(moduleId).data(),
                packet->chunkId,
                payloadString,
                requestHandle
            );
        }
        else if (actionType == RawDataActionType::REPORT && payloadLength >= sizeof(RawDataReportPayload))
        {
            const RawDataReportPayload* packet = (const RawDataReportPayload*)payloadPtr;

            char missingsBuffer[200] = "[";
            bool successfulTransmission = true;
            for (u32 i = 0; i < sizeof(packet->missings) / sizeof(packet->missings[0]); i++)
            {
                if (packet->missings[i] != 0)
                {
                    char singleMissingBuffer[50];
                    snprintf(singleMissingBuffer, sizeof(singleMissingBuffer), "%u", packet->missings[i]);

                    if (!successfulTransmission) 
                    {
                        strcat(missingsBuffer, ",");
                    }
                    strcat(missingsBuffer, singleMissingBuffer);

                    successfulTransmission = false;
                }
            }

            strcat(missingsBuffer, "]");

            logjson("DEBUG",
                "{"
                    "\"nodeId\":%u,"
                    "\"type\":\"raw_data_report\","
                    "\"module\":%s,"
                    "\"missing\":%s,"
                    "\"requestHandle\":%u"
                "}" SEP,
                senderId,
                Utility::GetModuleIdString(moduleId).data(),
                missingsBuffer,
                requestHandle
            );
        }
        else if (actionType == RawDataActionType::REPORT_DESIRED)
        {
            logjson("NODE",
                "{"
                "\"nodeId\":%u,"
                "\"type\":\"raw_data_report_desired\","
                "\"module\":%s,"
                "\"requestHandle\":%u"
                "}" SEP,
                senderId,
                Utility::GetModuleIdString(moduleId).data(),
                requestHandle
            );
        }
        else
        {
            SIMEXCEPTION(GotUnsupportedActionTypeException); //LCOV_EXCL_LINE assertion
        }
    }
    else if (packetHeader->messageType == MessageType::MODULE_RAW_DATA_LIGHT)
    {
        NodeId senderId = 0;
        ModuleIdWrapper moduleId = INVALID_WRAPPED_MODULE_ID;
        RawDataProtocol protocolId = RawDataProtocol::UNSPECIFIED;
        const u8* payloadPtr = nullptr;
        MessageLength payloadLength;
        u8 requestHandle = 0;

        const RawDataLight* packet = (const RawDataLight*)packetHeader;
        const RawDataLightVendor* packetVendor = (const RawDataLightVendor*)packetHeader;

        if(!Utility::IsVendorModuleId(packet->moduleId)){
            senderId = packet->connHeader.sender;
            moduleId = Utility::GetWrappedModuleId(packet->moduleId);
            requestHandle = packet->requestHandle;
            protocolId = packet->protocolId;
            payloadPtr = packet->payload;
            payloadLength = sendData->dataLength - SIZEOF_RAW_DATA_LIGHT_PACKET;
        } else if(sendData->dataLength >= SIZEOF_RAW_DATA_LIGHT_VENDOR_PACKET){
            senderId = packetVendor->connHeader.sender;
            moduleId = packetVendor->moduleId;
            requestHandle = packetVendor->requestHandle;
            protocolId = packetVendor->protocolId;
            payloadPtr = packetVendor->payload;
            payloadLength = sendData->dataLength - SIZEOF_RAW_DATA_LIGHT_VENDOR_PACKET;
        } else {
            SIMEXCEPTION(PacketTooSmallException); //LCOV_EXCL_LINE assertion
        }

        char payloadString[MAX_MESH_PACKET_SIZE];
        Logger::ConvertBufferToBase64String(payloadPtr, payloadLength, payloadString, sizeof(payloadString));

        logjson("DEBUG",
            "{"
                "\"nodeId\":%u,"
                "\"type\":\"raw_data_light\","
                "\"module\":%s,"
                "\"protocol\":%u,"
                "\"payload\":\"%s\","
                "\"requestHandle\":%u"
            "}" SEP,
            senderId,
            Utility::GetModuleIdString(moduleId).data(),
            (u32)protocolId,
            payloadString,
            requestHandle
        );
        
    }
    else if (packetHeader->messageType == MessageType::CAPABILITY)
    {
        if (sendData->dataLength >= sizeof(CapabilityHeader)) 
        {
            CapabilityHeader const * header = (CapabilityHeader const *)packetHeader;
            if (header->actionType == CapabilityActionType::REQUESTED)
            {
                isSendingCapabilities = true;
                firstCallForCurrentCapabilityModule = true;
                timeSinceLastCapabilitySentDs = TIME_BETWEEN_CAPABILITY_SENDINGS_DS; //Immediately send first capability uppon next timerEventHandler call.
                capabilityRetrieverModuleIndex = 0;
                capabilityRetrieverLocal = 0;
                capabilityRetrieverGlobal = 0;

                logt("NODE", "Capabilities are requested");
            }
            else if (header->actionType == CapabilityActionType::ENTRY)
            {
                if (sendData->dataLength >= sizeof(CapabilityEntryMessage))
                {
                    CapabilityEntryMessage const * message = (CapabilityEntryMessage const *)packetHeader;

                    char buffer[sizeof(message->entry.modelName) + 1]; //Buffer to make sure we have a terminating zero.

                    //Several logjson calls to go easy on stack size
                    logjson_partial("NODE", "{");
                    logjson_partial("NODE",        "\"nodeId\":%u,", message->header.header.sender);
                    logjson_partial("NODE",        "\"type\":\"capability_entry\",");
                    logjson_partial("NODE",        "\"index\":%u,", message->index);
                    logjson_partial("NODE",        "\"capabilityType\":%u,", (u32)message->entry.type);
                    CheckedMemcpy(buffer, message->entry.manufacturer, sizeof(message->entry.manufacturer));
                    buffer[sizeof(message->entry.manufacturer)] = '\0';
                    logjson_partial("NODE",        "\"manufacturer\":\"%s\",", buffer);
                    CheckedMemcpy(buffer, message->entry.modelName, sizeof(message->entry.modelName));
                    buffer[sizeof(message->entry.modelName)] = '\0';
                    logjson_partial("NODE",        "\"model\":\"%s\",", buffer);
                    CheckedMemcpy(buffer, message->entry.revision, sizeof(message->entry.revision));
                    buffer[sizeof(message->entry.revision)] = '\0';
                    logjson_partial("NODE",        "\"revision\":\"%s\"", buffer);
                    logjson("NODE", "}" SEP);
                }
                else
                {
                    SIMEXCEPTION(PacketTooSmallException); //LCOV_EXCL_LINE assertion
                }
            }
            else if (header->actionType == CapabilityActionType::END)
            {
                if (sendData->dataLength >= sizeof(CapabilityEndMessage))
                {
                    CapabilityEndMessage const * message = (CapabilityEndMessage const *)packetHeader;
                    logjson("NODE", 
                        "{"
                            "\"nodeId\":%u,"
                            "\"type\":\"capability_end\","
                            "\"amount\":%u"
                        "}" SEP,
                        message->header.header.sender,
                        message->amountOfCapabilities
                    );
                }
                else
                {
                    SIMEXCEPTION(PacketTooSmallException); //LCOV_EXCL_LINE assertion
                }
            }
        }
        else
        {
            SIMEXCEPTION(PacketTooSmallException); //LCOV_EXCL_LINE assertion
        }
    }

    else if (packetHeader->messageType == MessageType::COMPONENT_SENSE && sendData->dataLength >= SIZEOF_COMPONENT_MESSAGE_HEADER)
    {
        ModuleIdWrapper moduleId = INVALID_WRAPPED_MODULE_ID;

        const char* messageTypeString = packetHeader->messageType == MessageType::COMPONENT_SENSE ? "component_sense" : "component_act";
        
        NodeId senderId;
        u8 requestHandle;
        u8 actionType;
        u16 component;
        u16 registerAddress;
        char payloadString[200];

        const ComponentMessageHeader* componentHeader = (const ComponentMessageHeader*)packetHeader;

        //We must first check if the first byte indicates a ModuleId or a VendorModuleId
        if (!Utility::IsVendorModuleId(componentHeader->moduleId))
        {
            const ConnPacketComponentMessage* data = (const ConnPacketComponentMessage*)packetHeader;

            moduleId = Utility::GetWrappedModuleId(componentHeader->moduleId);

            senderId = data->componentHeader.header.sender;
            requestHandle = data->componentHeader.requestHandle;
            actionType = data->componentHeader.actionType;
            component = data->componentHeader.component;
            registerAddress = data->componentHeader.registerAddress;

            MessageLength payloadLength = sendData->dataLength - sizeof(data->componentHeader);
            Logger::ConvertBufferToBase64String(data->payload, payloadLength, payloadString, sizeof(payloadString));

        }
        else if(Utility::IsVendorModuleId(componentHeader->moduleId) && sendData->dataLength >= SIZEOF_COMPONENT_MESSAGE_HEADER_VENDOR)
        {
            const ConnPacketComponentMessageVendor* data = (const ConnPacketComponentMessageVendor*)packetHeader;

            moduleId = (ModuleIdWrapper)data->componentHeader.moduleId;

            senderId = data->componentHeader.header.sender;
            requestHandle = data->componentHeader.requestHandle;
            actionType = data->componentHeader.actionType;
            component = data->componentHeader.component;
            registerAddress = data->componentHeader.registerAddress;

            MessageLength payloadLength = sendData->dataLength - sizeof(data->componentHeader);
            Logger::ConvertBufferToBase64String(data->payload, payloadLength, payloadString, sizeof(payloadString));
        }
        else {
            return;
        }

        logjson("NODE", "{\"nodeId\":%u,"
            "\"type\":\"%s\","
            "\"module\":%s,"
            "\"requestHandle\":%u,"
            "\"actionType\":%u,"
            "\"component\":\"0x%04X\","
            "\"register\":\"0x%04X\","
            "\"payload\":\"%s\""
            "}" SEP,

            senderId,
            messageTypeString,
            Utility::GetModuleIdString(moduleId).data(),
            requestHandle,
            actionType,
            component,
            registerAddress,
            payloadString);

    }

    else if (packetHeader->messageType == MessageType::COMPONENT_ACT)
    {
        ConnPacketComponentMessage const* packet = (ConnPacketComponentMessage const*)packetHeader;

        char payload[50];
        MessageLength payloadLength = sendData->dataLength - sizeof(packet->componentHeader);
        Logger::ConvertBufferToHexString(packet->payload, payloadLength, payload, sizeof(payload));
        logt("NODE", "component_act payload = %s", payload);
    }
#if IS_ACTIVE(SIG_MESH)
    //Forwards tunneled SIG mesh messages to the implementation
    else if (packetHeader->messageType == MessageType::SIG_MESH_SIMPLE && sendData->dataLength >= SIZEOF_SIMPLE_SIG_MESSAGE)
    {
        GS->sig.SigMessageReceivedHandler((const SimpleSigMessage*)packetHeader, sendData->dataLength);
    }
#endif
}

DeliveryPriority Node::GetPriorityOfMessage(const u8* data, MessageLength size)
{
    if (size >= SIZEOF_CONN_PACKET_HEADER)
    {
        const ConnPacketHeader* header = (const ConnPacketHeader*)data;
        if (header->messageType == MessageType::CLUSTER_WELCOME
            || header->messageType == MessageType::CLUSTER_ACK_1
            || header->messageType == MessageType::CLUSTER_ACK_2
            || header->messageType == MessageType::UPDATE_CONNECTION_INTERVAL
            || header->messageType == MessageType::CLUSTER_INFO_UPDATE
            || header->messageType == MessageType::DATA_1_VITAL)
        {
            return DeliveryPriority::VITAL;
        }
         // 檢查是否為 GENERATE_LOAD_CHUNK 消息，如果是則使用設定的 priority
        if (header->messageType == MessageType::MODULE_TRIGGER_ACTION && size >= SIZEOF_CONN_PACKET_MODULE)
        {
            const ConnPacketModule* packet = (const ConnPacketModule*)data;
            if (packet->moduleId == ModuleId::NODE 
                && packet->actionType == (u8)NodeModuleTriggerActionMessages::GENERATE_LOAD_CHUNK)
            {
                // 檢查 payload 是否包含優先級標記
                const MessageLength payloadLength = size - SIZEOF_CONN_PACKET_MODULE;
                if (payloadLength > 0 && (packet->data[0] & 0xF0) == generateLoadPriorityMarker) {
                    // 從 payload 的第一個字節提取優先級（低 4 位）
                    u8 payloadPriority = packet->data[0] & 0x0F;
                    return (DeliveryPriority)payloadPriority;
                }

                // 如果沒有優先級標記，使用 generateLoadPriority（向後兼容）
                // 0: VITAL, 1: HIGH, 2: MEDIUM, 3: LOW
                return (DeliveryPriority)generateLoadPriority;
            }
        }
    }
    return DeliveryPriority::INVALID;
}

//Processes incoming CLUSTER_INFO_UPDATE packets
/*
 #########################################################################################################
 ### Advertising and Receiving advertisements
 #########################################################################################################
 */
#define ________________ADVERTISING___________________
                                                                                    
//Start to broadcast our own clusterInfo, set ackID if we want to have an ack or an ack response
void Node::UpdateJoinMePacket()
{
    if (configuration.networkId == 0) return;
    if (meshAdvJobHandle == nullptr) return;
    // 额外检查：防止指针被损坏为无效值
    if ((uintptr_t)meshAdvJobHandle == (uintptr_t)0xFFFFFFFF) {
        logt("ERROR", "meshAdvJobHandle is corrupted: 0x%X", (uintptr_t)meshAdvJobHandle);
        return;
    }
    if (GET_DEVICE_TYPE() == DeviceType::ASSET) return;

    SetTerminalTitle();

    u8* buffer = meshAdvJobHandle->advData;

    AdvPacketHeader* advPacket = (AdvPacketHeader*)buffer;
    advPacket->flags.len = SIZEOF_ADV_STRUCTURE_FLAGS-1; //minus length field itself
    advPacket->flags.type = (u8)BleGapAdType::TYPE_FLAGS;
    advPacket->flags.flags = FH_BLE_GAP_ADV_FLAG_LE_GENERAL_DISC_MODE | FH_BLE_GAP_ADV_FLAG_BR_EDR_NOT_SUPPORTED;

    advPacket->manufacturer.len = (SIZEOF_ADV_STRUCTURE_MANUFACTURER + SIZEOF_ADV_PACKET_STUFF_AFTER_MANUFACTURER + SIZEOF_ADV_PACKET_PAYLOAD_JOIN_ME_V0) - 1;
    advPacket->manufacturer.type = (u8)BleGapAdType::TYPE_MANUFACTURER_SPECIFIC_DATA;
    advPacket->manufacturer.companyIdentifier = MESH_COMPANY_IDENTIFIER;

    advPacket->meshIdentifier = MESH_IDENTIFIER;
    advPacket->networkId = configuration.networkId;
    advPacket->messageType = ManufacturerSpecificMessageType::JOIN_ME_V0;

    //Build a JOIN_ME packet and set it in the advertisement data
    AdvPacketPayloadJoinMeV0* packet = (AdvPacketPayloadJoinMeV0*)(buffer+SIZEOF_ADV_PACKET_HEADER);
    packet->sender = configuration.nodeId;
    packet->clusterId = this->clusterId;
    packet->clusterSize = this->clusterSize;
    // original code
    // packet->freeMeshInConnections = GS->cm.freeMeshInConnections;
    // new : sink has no free in connections
    if (GET_DEVICE_TYPE() == DeviceType::SINK) {
        packet->freeMeshInConnections = 0;
    }
    else{
        packet->freeMeshInConnections = GS->cm.freeMeshInConnections;
    }
    packet->freeMeshOutConnections = GS->cm.freeMeshOutConnections;

    //A leaf only has one free in connection
    if(GET_DEVICE_TYPE() == DeviceType::LEAF){
        if(GS->cm.freeMeshInConnections > 0) {
            packet->freeMeshInConnections = 1;
        }
        packet->freeMeshOutConnections = 0;
    }

    StatusReporterModule* statusMod = (StatusReporterModule*)this->GetModuleById(ModuleId::STATUS_REPORTER_MODULE);
    if(statusMod != nullptr){
        packet->batteryRuntime = statusMod->GetBatteryVoltage();
    } else {
        packet->batteryRuntime = 0;
    }

    packet->txPower = Conf::defaultDBmTX;
    packet->deviceType = GET_DEVICE_TYPE();
    packet->hopsToSink = GS->cm.GetMeshHopsToShortestSink(nullptr);
    packet->meshWriteHandle = meshService.sendMessageCharacteristicHandle.valueHandle;

    //We only use the concept of ackIds if we only use one mesh inConnection
    //Otherwhise, we do not need to use it as a partner can use our free inConnection
    if (GS->config.meshMaxInConnections == 1) {
        if (currentAckId != 0)
        {
            packet->ackField = currentAckId;

        }
        else {
            packet->ackField = 0;
        }
    }

    meshAdvJobHandle->advDataLength = SIZEOF_ADV_PACKET_HEADER + SIZEOF_ADV_PACKET_PAYLOAD_JOIN_ME_V0;

    logt("JOIN", "JOIN_ME updated clusterId:%x, clusterSize:%d, freeIn:%u, freeOut:%u, handle:%u, ack:%u", packet->clusterId, packet->clusterSize, packet->freeMeshInConnections, packet->freeMeshOutConnections, packet->meshWriteHandle, packet->ackField);

    logjson("SIM", "{\"type\":\"update_joinme\",\"clusterId\":%u,\"clusterSize\":%d}" SEP, clusterId, clusterSize);

    
    //Stop advertising if we are already connected as a leaf. Necessary for EoModule
    if(GET_DEVICE_TYPE() == DeviceType::LEAF && GS->cm.freeMeshInConnections == 0){
        meshAdvJobHandle->slots = 0;
    } else if(GET_DEVICE_TYPE() == DeviceType::LEAF){
        meshAdvJobHandle->slots = 5;
    }


    GS->advertisingController.RefreshJob(meshAdvJobHandle);
}


//This can be called to temporarily broadcast the join_me packet very frequently, e.g. if we want to reconnect
void Node::StartFastJoinMeAdvertising()
{
    //Immediately start a fast advertisement to speed up the reconnection
    AdvJob job = {
        AdvJobTypes::IMMEDIATE,
        10, //10 Slot * timer interval
        0, //Delay
        MSEC_TO_UNITS(20, CONFIG_UNIT_0_625_MS), //AdvInterval
        0, //AdvChannel
        0, //CurrentSlots
        0, //CurrentDelay
        FruityHal::BleGapAdvType::ADV_IND, //Advertising Mode
        {}, //AdvData
        3, //AdvDataLength
        {0}, //ScanData
        0 //ScanDataLength
    };

    //Copy the content of the current join_me packet
    CheckedMemcpy(job.advData, meshAdvJobHandle->advData, ADV_PACKET_MAX_SIZE);
    job.advDataLength = meshAdvJobHandle->advDataLength;

    //Add the job, it will be removed after it has no more slots left
    GS->advertisingController.AddJob(job);
}

//STEP 3: After collecting all available clusters, we want to connect to the best cluster that is available
//If the other clusters were not good and we have something better, we advertise it.
Node::DecisionStruct Node::DetermineBestClusterAvailable(void)
{
    // //FruityMesh original code
    // DecisionStruct result = { DecisionResult::NO_NODES_FOUND, 0, 0 };

    // joinMeBufferPacket* bestClusterAsMaster = DetermineBestClusterAsMaster();

    // //If we still do not have a freeOutConnection, we have no viable cluster to connect to
    // if (GS->cm.freeMeshOutConnections > 0)
    // {
    //     //Now, if we want to be a master in the connection, we simply answer the ad packet that
    //     //informs us about that cluster
    //     if (bestClusterAsMaster != nullptr)
    //     {
    //         currentAckId = 0;

    //         FruityHal::BleGapAddr address = bestClusterAsMaster->addr;

    //         //Choose a different connection interval for leaf nodes
    //         u16 connectionIv = Conf::GetInstance().meshMinConnectionInterval;
    //         if(bestClusterAsMaster->payload.deviceType == DeviceType::LEAF){
    //             connectionIv = MSEC_TO_UNITS(90, CONFIG_UNIT_1_25_MS);
    //         }

    //         ErrorType err = GS->cm.ConnectAsMaster(bestClusterAsMaster->payload.sender, &address, bestClusterAsMaster->payload.meshWriteHandle, connectionIv);

    //         //Note the time that we tried to connect to this node so that we can blacklist it for some time if it does not work
    //         if (err == ErrorType::SUCCESS) {
    //             bestClusterAsMaster->lastConnectAttemptDs = GS->appTimerDs;
    //             if(bestClusterAsMaster->attemptsToConnect <= 20) bestClusterAsMaster->attemptsToConnect++;
    //         }

    //         result.result = DecisionResult::CONNECT_AS_MASTER;
    //         result.preferredPartner = bestClusterAsMaster->payload.sender;
    //         return result;
    //     }
    // }

    // //If no good cluster could be found (all are bigger than mine)
    // //Find the best cluster that should connect to us (we as slave)
    // currentAckId = 0;
    // joinMeBufferPacket* bestClusterAsSlave = DetermineBestClusterAsSlave();

    // //Set our ack field to the best cluster that we want to be a part of
    // if (bestClusterAsSlave != nullptr)
    // {
    //     currentAckId = bestClusterAsSlave->payload.clusterId;

    //     logt("DECISION", "Other clusters are bigger, we are going to be a slave of %u", currentAckId);

    //     //For nodes with only 1 meshInConnection, we must disconnect from a cluster if a bigger cluster is found nearby
    //     if (GS->config.meshMaxInConnections == 1) {

    //         //Check if we have a recently established connection and do not disconnect if yes bofore the handshake has not timed out
    //         bool freshConnectionAvailable = false;
    //         BaseConnections conns = GS->cm.GetBaseConnections(ConnectionDirection::INVALID);
    //         for (u32 i = 0; i < conns.count; i++) {
    //             BaseConnectionHandle conn = conns.handles[i];
    //             if (conn) {
    //                 if (conn.GetCreationTimeDs() + Conf::meshHandshakeTimeoutDs > GS->appTimerDs) {
    //                     freshConnectionAvailable = true;
    //                     break;
    //                 }
    //             }
    //         }
    //         //Only if we are not currently doing a handshake and if we do not have a freeInConnection
    //         if (!freshConnectionAvailable && GS->cm.freeMeshInConnections == 0) {
    //             if (
    //                 //Check if we have either different clusterSizes or if similar, only disconnect randomly
    //                 //to prevent recurrent situations where two nodes will always disconnect at the same time
    //                 GetClusterSize() != bestClusterAsSlave->payload.clusterSize
    //                 || Utility::GetRandomInteger() < UINT32_MAX / 4
    //             ) {
    //                 GS->cm.ForceDisconnectOtherMeshConnections(nullptr, AppDisconnectReason::SHOULD_WAIT_AS_SLAVE);

    //                 SetClusterSize(1);
    //                 clusterId = GenerateClusterID();
    //             }
    //         }
    //     }

    //     UpdateJoinMePacket();

    //     result.result = DecisionResult::CONNECT_AS_SLAVE;
    //     result.preferredPartner = bestClusterAsSlave->payload.sender;
    //     return result;
    // }

    // logt("DECISION", "no cluster found");

    // result.result = DecisionResult::NO_NODES_FOUND;
    // return result;
    
    // // fruityMesh original code

    // new: FruityMesh modified code
    DecisionStruct result = { DecisionResult::NO_NODES_FOUND, 0, 0 };
    
    // new: 取得當前設備類型
    DeviceConfiguration config;
    ErrorType err = FruityHal::GetDeviceConfiguration(config);
    DeviceType deviceType;
    if (err == ErrorType::SUCCESS) {
        deviceType = static_cast<DeviceType>(config.deviceType);
    }

    // new: 如果是 Sink，優先建立 Mesh (當 Master)
    if (deviceType == DeviceType::SINK && GS->cm.freeMeshOutConnections > 0) {
         
        // new: 嘗試作為 Master 連接最好的節點
        joinMeBufferPacket* bestClusterAsMaster = DetermineBestClusterAsMaster();
        if (GS->cm.freeMeshOutConnections > 0 && bestClusterAsMaster != nullptr) {
            currentAckId = 0;

            FruityHal::BleGapAddr address = bestClusterAsMaster->addr;

            u16 connectionIv = Conf::GetInstance().meshMinConnectionInterval;
            if (bestClusterAsMaster->payload.deviceType == DeviceType::LEAF) {
                connectionIv = MSEC_TO_UNITS(90, CONFIG_UNIT_1_25_MS);
            }

            ErrorType err = GS->cm.ConnectAsMaster(bestClusterAsMaster->payload.sender, &address, bestClusterAsMaster->payload.meshWriteHandle, connectionIv);
            if (err == ErrorType::SUCCESS) {
                bestClusterAsMaster->lastConnectAttemptDs = GS->appTimerDs;
                if (bestClusterAsMaster->attemptsToConnect <= 20) {
                    bestClusterAsMaster->attemptsToConnect++;
                }
            }

            result.result = DecisionResult::CONNECT_AS_MASTER;
            result.preferredPartner = bestClusterAsMaster->payload.sender;
            return result;
        }
    }else {
        //new: 先以slave找出最好的master進行連線
        //If no good cluster could be found (all are bigger than mine)
        //Find the best cluster that should connect to us (we as slave)
        currentAckId = 0;
        joinMeBufferPacket* bestClusterAsSlave = DetermineBestClusterAsSlave();

        if(GET_DEVICE_TYPE() == DeviceType::SINK){
            bestClusterAsSlave = nullptr;
        }

        //Set our ack field to the best cluster that we want to be a part of
        if (bestClusterAsSlave != nullptr)
        {
            currentAckId = bestClusterAsSlave->payload.clusterId;
            logt("DECISION", "Other clusters are bigger, we are going to be a slave of %u", currentAckId);
             //For nodes with only 1 meshInConnection, we must disconnect from a cluster if a bigger cluster is found nearby
             if (GS->config.meshMaxInConnections == 1) {
 
                //Check if we have a recently established connection and do not disconnect if yes bofore the handshake has not timed out
                bool freshConnectionAvailable = false;
                BaseConnections conns = GS->cm.GetBaseConnections(ConnectionDirection::INVALID);
                for (u32 i = 0; i < conns.count; i++) {
                    BaseConnectionHandle conn = conns.handles[i];
                    if (conn) {
                        if (conn.GetCreationTimeDs() + Conf::meshHandshakeTimeoutDs > GS->appTimerDs) {
                            freshConnectionAvailable = true;
                            break;
                        }
                    }
                }
                //Only if we are not currently doing a handshake and if we do not have a freeInConnection
                if (!freshConnectionAvailable && GS->cm.freeMeshInConnections == 0) {
                    if (
                        //Check if we have either different clusterSizes or if similar, only disconnect randomly
                        //to prevent recurrent situations where two nodes will always disconnect at the same time
                        GetClusterSize() != bestClusterAsSlave->payload.clusterSize
                        || Utility::GetRandomInteger() < UINT32_MAX / 4
                    ) {
                        GS->cm.ForceDisconnectOtherMeshConnections(nullptr, AppDisconnectReason::SHOULD_WAIT_AS_SLAVE);

                        SetClusterSize(1);
                        clusterId = GenerateClusterID();
                    }
                }
            }
            UpdateJoinMePacket();
 
            result.result = DecisionResult::CONNECT_AS_SLAVE;
            result.preferredPartner = bestClusterAsSlave->payload.sender;
            return result;
        }

        //new: 如果沒有找到合適的 master，再以Master找到適合的 Slave 進行連線
        joinMeBufferPacket* bestClusterAsMaster = DetermineBestClusterAsMaster();

        //If we still do not have a freeOutConnection, we have no viable cluster to connect to
        if (GS->cm.freeMeshOutConnections > 0)
        {
            //Now, if we want to be a master in the connection, we simply answer the ad packet that
            //informs us about that cluster
            if (bestClusterAsMaster != nullptr)
            {
                currentAckId = 0;

                FruityHal::BleGapAddr address = bestClusterAsMaster->addr;

                //Choose a different connection interval for leaf nodes
                u16 connectionIv = Conf::GetInstance().meshMinConnectionInterval;
                if(bestClusterAsMaster->payload.deviceType == DeviceType::LEAF){
                    connectionIv = MSEC_TO_UNITS(90, CONFIG_UNIT_1_25_MS);
                }

                ErrorType err = GS->cm.ConnectAsMaster(bestClusterAsMaster->payload.sender, &address, bestClusterAsMaster->payload.meshWriteHandle, connectionIv);

                //Note the time that we tried to connect to this node so that we can blacklist it for some time if it does not work
                if (err == ErrorType::SUCCESS) {
                    bestClusterAsMaster->lastConnectAttemptDs = GS->appTimerDs;
                    if(bestClusterAsMaster->attemptsToConnect <= 20) bestClusterAsMaster->attemptsToConnect++;
                }

                result.result = DecisionResult::CONNECT_AS_MASTER;
                result.preferredPartner = bestClusterAsMaster->payload.sender;
                return result;
            }
        }
        
        logt("DECISION", "no cluster found");
        
        result.result = DecisionResult::NO_NODES_FOUND;
        return result;
    }

    result.result = DecisionResult::NO_NODES_FOUND;
    return result;
}

u32 Node::ModifyScoreBasedOnPreferredPartners(u32 score, NodeId partner) const
{
    if (score > 0 && !IsPreferredConnection(partner))
    {
        if (GS->config.configuration.preferredConnectionMode == PreferredConnectionMode::PENALTY)
        {
            score /= 10;
            if (score < 1) score = 1; //If the mode is set to penalty, we don't want to ignore any possible cluster.
        }
        else if (GS->config.configuration.preferredConnectionMode == PreferredConnectionMode::IGNORED)
        {
            score = 0;
        }
        else
        {
            //This PreferredConnectionMode is not implemented.
            SIMEXCEPTION(IllegalStateException); //LCOV_EXCL_LINE assertion
        }
    }

    return score;
}

joinMeBufferPacket * Node::DetermineBestCluster(u32(Node::*clusterRatingFunction)(const joinMeBufferPacket &packet) const)
{
    u32 bestScore = 0;
    joinMeBufferPacket* bestCluster = nullptr;

    for (u32 i = 0; i < joinMePackets.size(); i++)
    {
        joinMeBufferPacket* packet = &joinMePackets[i];
        if (packet->payload.sender == 0) continue;

        u32 score = (this->*clusterRatingFunction)(*packet);
        if (score > bestScore)
        {
            bestScore = score;
            bestCluster = packet;
        }
    }
    return bestCluster;
}

joinMeBufferPacket* Node::DetermineBestClusterAsSlave()
{
    return DetermineBestCluster(&Node::CalculateClusterScoreAsSlave);
}

joinMeBufferPacket* Node::DetermineBestClusterAsMaster()
{
    return DetermineBestCluster(&Node::CalculateClusterScoreAsMaster);
}

//Calculates the score for a cluster
//Connect to big clusters but big clusters must connect nodes that are not able 
u32 Node::CalculateClusterScoreAsMaster(const joinMeBufferPacket& packet) const
{
    // if(1) return 0;
    //new test if slave node id > now node id return 0; 
    //if (packet.payload.sender < configuration.nodeId) return 0;    
    // if (packet.payload.sender != 5 && packet.payload.sender != 6) return 0; 
    // if (packet.payload.sender != 3 && packet.payload.sender != 4) return 0;  
    // if (packet.payload.sender != 1)  return 0; 
    if (packet.payload.sender != 2)  return 0; 
    // if (packet.payload.sender != 3)  return 0; 
    // if (packet.payload.sender != 4)  return 0; 
    // if (packet.payload.sender != 5)  return 0; 
    // if (packet.payload.sender != 6)  return 0; 
    
    // if (packet.payload.sender != 2 && packet.payload.sender != 3 && packet.payload.sender != 6)  return 0; 

    //new: 取得當前設備類型
    DeviceConfiguration config;
    ErrorType err = FruityHal::GetDeviceConfiguration(config);
    DeviceType deviceType;
    if (err == ErrorType::SUCCESS)
    deviceType = static_cast<DeviceType>(config.deviceType);

    //If the packet is too old, filter it out
    if (GS->appTimerDs - packet.receivedTimeDs > MAX_JOIN_ME_PACKET_AGE_DS) return 0;

    //If we are already connected to that cluster, the score is 0
    if (packet.payload.clusterId == this->clusterId) return 0;

    //If there are zero free in connections, we cannot connect as master
    if (packet.payload.freeMeshInConnections == 0) return 0;

    //If the other node wants to connect as a slave to another cluster, do not connect
    if (packet.payload.ackField != 0 && packet.payload.ackField != this->clusterId) return 0;

    // //If the other cluster is bigger, we cannot connect as master
    // if (packet.payload.clusterSize > GetClusterSize()) return 0;
    //new: add "&& GET_DEVICE_TYPE() != DeviceType::SINK" to prevent sink from connecting to be a slave
    if (packet.payload.clusterSize > GetClusterSize() && GET_DEVICE_TYPE() != DeviceType::SINK) return 0;


    //Check if we recently tried to connect to him and blacklist him for a short amount of time
    if (
        packet.lastConnectAttemptDs != 0
        && packet.attemptsToConnect > connectAttemptsBeforeBlacklisting
        && packet.lastConnectAttemptDs + SEC_TO_DS(1) * packet.attemptsToConnect > GS->appTimerDs) {
        SIMSTATCOUNT("tempBlacklist");
        logt("NODE", "temporarily blacklisting node %u, attempts: %u", packet.payload.sender, packet.attemptsToConnect);
        return 0;
    }

    //Do not connect if we are already connected to that partner
    if (GS->cm.GetMeshConnectionToPartner(packet.payload.sender)) return 0;

    //Connection should have a minimum of stability
    if(packet.rssi < STABLE_CONNECTION_RSSI_THRESHOLD) return 0;

    u32 rssiScore = 100 + packet.rssi;

    //If we are a leaf node, we must not connect to anybody
    if(GET_DEVICE_TYPE() == DeviceType::LEAF) return 0;

    //Free in connections are best, free out connections are good as well
    //TODO: RSSI should be factored into the score as well, maybe battery runtime, device type, etc...
    u32 score = (u32)(packet.payload.freeMeshInConnections) * 10000 + (u32)(packet.payload.freeMeshOutConnections) * 100 + rssiScore;

    return ModifyScoreBasedOnPreferredPartners(score, packet.payload.sender);
}

//If there are only bigger clusters around, we want to find the best
//And set its id in our ack field
u32 Node::CalculateClusterScoreAsSlave(const joinMeBufferPacket& packet) const
{    
    //new: 取得當前設備類型
    DeviceConfiguration config;
    ErrorType err = FruityHal::GetDeviceConfiguration(config);
    DeviceType deviceType;
    if (err == ErrorType::SUCCESS)
    deviceType = static_cast<DeviceType>(config.deviceType);

    if (deviceType == DeviceType::SINK) return 0;

    //if (packet.payload.hopsToSink < 0) return 0;
 
    if (packet.payload.freeMeshOutConnections == 0) return 0;

    //If the packet is too old, filter it out
    if (GS->appTimerDs - packet.receivedTimeDs > MAX_JOIN_ME_PACKET_AGE_DS) return 0;

    //If we are already connected to that cluster, the score is 0
    if (packet.payload.clusterId == this->clusterId) return 0;

    //Do not check for freeOut == 0 as the partner will probably free up a conneciton for us and we should be ready

    // //We will only be a slave of a bigger or equal cluster
    // if (packet.payload.clusterSize < GetClusterSize()) return 0;
    //new: add "&& packet.payload.deviceType != DeviceType::SINK" to prevent sink from connecting to be a slave
    if (packet.payload.clusterSize < GetClusterSize() && packet.payload.deviceType != DeviceType::SINK) return 0;

    //Connection should have a minimum of stability
    if(packet.rssi < STABLE_CONNECTION_RSSI_THRESHOLD) return 0;

    u32 rssiScore = 100 + packet.rssi;

    //new: add sink node weight score 
    u32 score = 0;
    if(packet.payload.deviceType == DeviceType::SINK){
        score = 100000;
    }
    score += (u32)(packet.payload.clusterSize) * 10000 + (u32)(packet.payload.freeMeshOutConnections) * 100 + rssiScore;

    // //Choose the one with the biggest cluster size, if there are more, prefer the most outConnections
    // u32 score = (u32)(packet.payload.clusterSize) * 10000 + (u32)(packet.payload.freeMeshOutConnections) * 100 + rssiScore;

    return ModifyScoreBasedOnPreferredPartners(score, packet.payload.sender);
}

bool Node::DoesBiggerKnownClusterExist()
{
    return DetermineBestClusterAsSlave() != nullptr;
}

void Node::ResetEmergencyDisconnect()
{
    emergencyDisconnectTimerDs = 0;
    if (emergencyDisconnectValidationConnectionUniqueId)
    {
        emergencyDisconnectValidationConnectionUniqueId.DisconnectAndRemove(AppDisconnectReason::EMERGENCY_DISCONNECT_RESET);
        emergencyDisconnectValidationConnectionUniqueId = MeshAccessConnectionHandle();
    }
}

void Node::SendGroupResponse(NodeId receiver, NodeModuleActionResponseMessages actionType, u8 requestHandle, NodeId group, AddDynamicGroupResponseMessageCode code)
{
    DynamicGroupResponseMessage responseMessage;
    CheckedMemset(&responseMessage, 0, sizeof(responseMessage));
    responseMessage.code = code;
    responseMessage.id = group;
    SendModuleActionMessage(
        MessageType::MODULE_ACTION_RESPONSE,
        receiver,
        (u8)actionType,
        0,
        (u8*)(&responseMessage),
        sizeof(responseMessage),
        false
    );
}

void Node::SendGroupResponse(NodeId receiver, NodeModuleActionResponseMessages actionType, u8 requestHandle, NodeId group, RecordStorageResultCode code)
{
    AddDynamicGroupResponseMessageCode transformedCode = AddDynamicGroupResponseMessageCode::SUCCESS;
    if (code != RecordStorageResultCode::SUCCESS)
    {
        static_assert((u32)RecordStorageResultCode::LAST_ENTRY < 255 - (u32)AddDynamicGroupResponseMessageCode::RECORD_STORAGE_ERROR_OFFSET, "Not enough room to embed error codes!");
        transformedCode = (AddDynamicGroupResponseMessageCode)((u32)code + (u32)AddDynamicGroupResponseMessageCode::RECORD_STORAGE_ERROR_OFFSET);
    }
    SendGroupResponse(receiver, actionType, requestHandle, group, transformedCode);
}

void Node::SaveRecordStorageDynamicGroup(NodeId receiver, NodeModuleActionResponseMessages actionType, u8 requestHandle, NodeId group)
{
    DynamicGroupSaveData saveData;
    CheckedMemset(&saveData, 0, sizeof(saveData));
    saveData.group = group;
    saveData.receiver = receiver;
    saveData.requestHandle = requestHandle;
    RecordStorageResultCode result = GS->recordStorage.SaveRecord(
        (u16)ModuleId::NODE,
        (u8*)&(configuration),
        sizeof(configuration),
        this,
        (u32)actionType,
        (u8*)&saveData,
        sizeof(saveData));
    if (result != RecordStorageResultCode::SUCCESS)
    {
        SendGroupResponse(receiver, actionType, requestHandle, group, result);
    }
    // => continues in RecordStorageEventHandler
}

//All advertisement packets are received here if they are valid
void Node::GapAdvertisementMessageHandler(const FruityHal::GapAdvertisementReportEvent& advertisementReportEvent)
{
    if (GET_DEVICE_TYPE() == DeviceType::ASSET) return;

    const u8* data = advertisementReportEvent.GetData();
    u16 dataLength = advertisementReportEvent.GetDataLength();

    const AdvPacketHeader* packetHeader = (const AdvPacketHeader*) data;

    if (packetHeader->messageType == ManufacturerSpecificMessageType::JOIN_ME_V0)
    {
        if (dataLength == SIZEOF_ADV_PACKET_JOIN_ME)
        {
            GS->logger.LogCustomCount(CustomErrorTypes::COUNT_JOIN_ME_RECEIVED);

            const AdvPacketJoinMeV0* packet = (const AdvPacketJoinMeV0*) data;

            logt("DISCOVERY", "JOIN_ME: sender:%u, clusterId:%x, clusterSize:%d, freeIn:%u, freeOut:%u, ack:%u", packet->payload.sender, packet->payload.clusterId, packet->payload.clusterSize, packet->payload.freeMeshInConnections, packet->payload.freeMeshOutConnections, packet->payload.ackField);

            //Look through the buffer and determine a space where we can put the packet in
            joinMeBufferPacket* targetBuffer = FindTargetBuffer(packet);

            //Now, we have the space for our packet and we fill it with the latest information
            if (targetBuffer != nullptr && packet->payload.clusterId != this->clusterId)
            {
                targetBuffer->addr.addr = advertisementReportEvent.GetPeerAddr();
                targetBuffer->addr.addr_type = advertisementReportEvent.GetPeerAddrType();
                targetBuffer->advType = advertisementReportEvent.IsConnectable() ? FruityHal::BleGapAdvType::ADV_IND : FruityHal::BleGapAdvType::ADV_NONCONN_IND;
                targetBuffer->rssi = advertisementReportEvent.GetRssi();
                targetBuffer->receivedTimeDs = GS->appTimerDs;

                targetBuffer->payload = packet->payload;
            }
        }
    }

}

joinMeBufferPacket* Node::FindTargetBuffer(const AdvPacketJoinMeV0* packet)
{
    joinMeBufferPacket* targetBuffer = nullptr;

    //First, look if a packet from this node is already in the buffer, if yes, we use this space
    for (u32 i = 0; i < joinMePackets.size(); i++)
    {
        targetBuffer = &joinMePackets[i];

        if (packet->payload.sender == targetBuffer->payload.sender)
        {
            logt("DISCOVERY", "Updated old buffer packet");
            return targetBuffer;
        }
    }
    targetBuffer = nullptr;

    //Next, we look if there's an empty space
    for (u32 i = 0; i < joinMePackets.size(); i++)
    {
        targetBuffer = &(joinMePackets[i]);

        if(targetBuffer->payload.sender == 0)
        {
            logt("DISCOVERY", "Used empty space");
            return targetBuffer;
        }
    }
    targetBuffer = nullptr;

    //Next, we can overwrite the oldest packet that we saved from our own cluster
    u32 oldestTimestamp = UINT32_MAX;
    for (u32 i = 0; i < joinMePackets.size(); i++)
    {
        joinMeBufferPacket* tmpPacket = &joinMePackets[i];

        if(tmpPacket->payload.clusterId == clusterId && tmpPacket->receivedTimeDs < oldestTimestamp){
            oldestTimestamp = tmpPacket->receivedTimeDs;
            targetBuffer = tmpPacket;
        }
    }

    if(targetBuffer != nullptr){
        logt("DISCOVERY", "Overwrote one from our own cluster");
        return targetBuffer;
    }

    //If there's still no space, we overwrite the oldest packet that we received, this will not fail
    //TODO: maybe do not use oldest one but worst candidate?? Use clusterScore on all packets to find the least interesting
    u32 minScore = UINT32_MAX;
    for (u32 i = 0; i < joinMePackets.size(); i++)
    {
        joinMeBufferPacket* tmpPacket = &joinMePackets[i];

        u32 score = 0;
        if (packet->payload.clusterSize >= clusterSize) {
            score = CalculateClusterScoreAsMaster(*tmpPacket);
        }
        else {
            score = CalculateClusterScoreAsSlave(*tmpPacket);
        }

        if(score < minScore){
            minScore = score;
            targetBuffer = tmpPacket;
        }
    }

    logt("DISCOVERY", "Overwrote worst packet from different cluster");
    return targetBuffer;
}

/*
 #########################################################################################################
 ### Advertising and Receiving advertisements
 #########################################################################################################
 */
#define ________________STATES___________________

void Node::ChangeState(DiscoveryState newState)
{
    // Single node should always be in high discovery
    if ((newState != DiscoveryState::HIGH) && (GS->node.GetClusterSize() < 2))
    {
        return;
    }

    if (currentDiscoveryState == newState || stateMachineDisabled || GET_DEVICE_TYPE() == DeviceType::ASSET){
        if ((currentDiscoveryState == DiscoveryState::HIGH) && (SEC_TO_DS((u32)Conf::GetInstance().highDiscoveryTimeoutSec) != 0))
        {
            currentStateTimeoutDs = SEC_TO_DS((u32)Conf::GetInstance().highDiscoveryTimeoutSec);
            nextDiscoveryState = DiscoveryState::LOW;
        }
        return;
    }

    currentDiscoveryState = newState;

    if (newState == DiscoveryState::HIGH)
    {
        logt("STATES", "-- DISCOVERY HIGH --");

        //Reset no nodes found counter
        noNodesFoundCounter = 0;

        currentStateTimeoutDs = SEC_TO_DS((u32)Conf::GetInstance().highDiscoveryTimeoutSec);
        nextDiscoveryState = Conf::GetInstance().highDiscoveryTimeoutSec == 0 ? DiscoveryState::INVALID : DiscoveryState::LOW;

        //Reconfigure the advertising and scanning jobs
        if (meshAdvJobHandle != nullptr){
            meshAdvJobHandle->advertisingInterval =    Conf::meshAdvertisingIntervalHigh;
            meshAdvJobHandle->slots = 5;
            GS->advertisingController.RefreshJob(meshAdvJobHandle);
        }

        GS->scanController.UpdateJobPointer(&p_scanJob, ScanState::HIGH, ScanJobState::ACTIVE);
    }
    else if (newState == DiscoveryState::LOW)
    {
        logt("STATES", "-- DISCOVERY LOW --");

        currentStateTimeoutDs = 0;
        nextDiscoveryState = DiscoveryState::INVALID;

        //Reconfigure the advertising and scanning jobs
        if (meshAdvJobHandle != nullptr) {
            meshAdvJobHandle->advertisingInterval = Conf::meshAdvertisingIntervalLow;
            GS->advertisingController.RefreshJob(meshAdvJobHandle);
        }
        ScanJob scanJob = ScanJob();
        scanJob.type = ScanState::LOW;
        scanJob.state = ScanJobState::ACTIVE;
        GS->scanController.RemoveJob(p_scanJob);
        p_scanJob = nullptr;

        p_scanJob = GS->scanController.AddJob(scanJob);
    }
    else if (newState == DiscoveryState::IDLE)
    {
        logt("STATES", "-- DISCOVERY IDLE --");

        nextDiscoveryState = DiscoveryState::INVALID;

        if (meshAdvJobHandle != nullptr) {
            meshAdvJobHandle->advertisingInterval = Conf::meshAdvertisingIntervalLow;
            GS->advertisingController.RefreshJob(meshAdvJobHandle);
        }

        GS->scanController.RemoveJob(p_scanJob);
        p_scanJob = nullptr;
    }
    else if (newState == DiscoveryState::OFF)
    {
        logt("STATES", "-- DISCOVERY OFF --");

        nextDiscoveryState = DiscoveryState::INVALID;

        GS->advertisingController.RemoveJob(meshAdvJobHandle);
        GS->scanController.RemoveJob(p_scanJob);
        p_scanJob = nullptr;
    }
}

void Node::DisableStateMachine(bool disable)
{
    stateMachineDisabled = disable;
}

//新加入功能調整connection interval
void Node::TimerEventHandler(u16 passedTimeDs)
{
     // State machine for staggered connection interval updates
    if (connUpdateIndex >= 0 && GS->appTimerDs >= nextConnUpdateAllowedTimeDs)
    {
        MeshConnections conns = GS->cm.GetMeshConnections(ConnectionDirection::INVALID);
        if (connUpdateIndex >= conns.count)
        {
            // Finished all connections
            logt("NODE", "Finished applying connection interval updates.");
            connUpdateIndex = -1;
            connUpdateIntervalMs = 0;
        }
        else
        {
            // Update the next connection
            MeshConnectionHandle connToUpdate = conns.handles[connUpdateIndex];
            if (connToUpdate && connToUpdate.IsHandshakeDone())
            {
                ErrorType err = UpdateConnectionInterval(connToUpdate.GetConnection()->connectionHandle, connUpdateIntervalMs);
                if (err == ErrorType::SUCCESS)
                {
                    // Success, move to the next one after a short delay
                    connUpdateIndex++;
                    nextConnUpdateAllowedTimeDs = GS->appTimerDs + 2; // 2 deciseconds = 200ms delay
                }
                else if (err == (ErrorType)17 /* NRF_ERROR_BUSY */)
                {
                    // Busy, retry the same index after a delay
                    nextConnUpdateAllowedTimeDs = GS->appTimerDs + SEC_TO_DS(1); // 1s delay
                }
                else
                {
                    // Other error, log it and move to the next connection to avoid getting stuck
                    logt("ERROR", "Skipping conn interval update for index %d due to error %u", connUpdateIndex, (u32)err);
                    connUpdateIndex++;
                    nextConnUpdateAllowedTimeDs = GS->appTimerDs + 2; // 2 deciseconds = 200ms delay
                }
            }
            else
            {
                // This connection is not valid or ready, skip it and try next one immediately
                connUpdateIndex++;
                nextConnUpdateAllowedTimeDs = GS->appTimerDs;
            }
        }
    }

    //delayTime
    if(delayTime > 0)
    {
        delayTime --;
    }
    else if (delayTime == 0)
    {
        delayTime = -1;
        const char* args[] = {
            "action", cmd[1], "node", "multi_generate_load", cmd[4], cmd[5], cmd[6], cmd[7], cmd[8]
        };
        TerminalCommandHandlerReturnType result = this->TerminalCommandHandler(args, 9);
    }
    //synctime    
    if(ssettime>0)
    {
        ssettime --;
    }
    else if (ssettime==0)
    {
        //Set the time for our node
        GS->timeManager.SetMasterTime(strtoul("1", nullptr, 10), 0, (i16)strtol("1", nullptr, 10));
        ssettime = -1;
    }

    //adjust time
    if(adjust>0)
    {
        adjust--;
    }
    else if (adjust==0)
    {
        GS->caltime+=errorIndex;
        adjust = -1;
    }

    //reporter delay
    if(delayReporter==1){
        //trace("appTimerDs : %u passedTimeDs : %u " EOL, GS->appTimerDs, passedTimeDs);
        //trace("Rtc : %u UtcMs : %u " EOL, FruityHal::GetRtcMs(), GS->timeManager.GetUtcTime());
        trace("Delaytimer : %u Utc : %u " EOL, GS->delaytimer, GS->timeManager.GetUtcTime());
        //trace("GS->caltick : %d",GS->caltick);
        trace("caltick : %u" EOL, GS->caltick);
        trace("timesynce : %u" EOL, GS->inittimeSinceSyncTime);
    }
    

    //reporter dis/enb
    if (flag == 1) {
        testdis++;
        //if(testdis==100){      
            if(switchReporter==1){
             trace("dis/enb switch" EOL);
            }   
        GS->cm.UpdateState();
        GS->cm.FillTransmitBuffers();//sure?
        testdis=0;
        //}
    }

    //multi_generate_load
    if (generate_load == 1){
        for (int i=0; i<10; i++){
            DYNAMIC_ARRAY(payloadBuffer, generateLoadPayloadSize);
            CheckedMemset(payloadBuffer, generateLoadMagicNumber, generateLoadPayloadSize);

            SendModuleActionMessage(
                MessageType::MODULE_TRIGGER_ACTION,
                generateLoadTarget,
                (u8)NodeModuleTriggerActionMessages::GENERATE_LOAD_CHUNK,
                generateLoadRequestHandle,
                payloadBuffer,
                generateLoadPayloadSize,
                false
            );
        }
    }

    currentStateTimeoutDs -= passedTimeDs;
    clusterSizeTransitionTimeoutDs -= passedTimeDs;

    //Check if we should switch states because of timeouts
    if (nextDiscoveryState != DiscoveryState::INVALID && currentStateTimeoutDs <= 0)
    {
        //Go to the next state
        ChangeState(nextDiscoveryState);
    }

    //Check if new cluster size should trigger discovery change
    if (!clusterSizeChangeHandled && clusterSizeTransitionTimeoutDs <= 0)
    {
        clusterSizeChangeHandled = true;
        if (clusterSize == GS->node.configuration.numberOfEnrolledDevices)
        {
            ChangeState(DiscoveryState::IDLE);
        }
        else if ((GS->node.configuration.numberOfEnrolledDevices != 0) && (clusterSize > GS->node.configuration.numberOfEnrolledDevices))
        {
            //If clustersize is bigger than number of enrolled devices there is some kind of misconfiguration. We should remove info about 
            //enrolled devices as it is invalid.
            SetEnrolledNodes(0, GS->node.configuration.nodeId);
            //We also need to exit discovery OFF state.
            ChangeState(DiscoveryState::LOW);
        }
        else if (clusterSize < GS->node.configuration.numberOfEnrolledDevices || GS->node.configuration.numberOfEnrolledDevices <= 1)
        {
            ChangeState(DiscoveryState::HIGH);
        }
    }

    if (DoesBiggerKnownClusterExist())
    {
        const u32 emergencyDisconnectTimerBackupDs = emergencyDisconnectTimerDs;
        emergencyDisconnectTimerDs += passedTimeDs;

        //If the emergencyDisconnectTimerTriggerDs was surpassed in this TimerEventHandler
        if(    emergencyDisconnectTimerBackupDs <  emergencyDisconnectTimerTriggerDs
            && emergencyDisconnectTimerDs       >= emergencyDisconnectTimerTriggerDs)
        {
            joinMeBufferPacket* bestCluster = DetermineBestClusterAsSlave();
            emergencyDisconnectValidationConnectionUniqueId = MeshAccessConnectionHandle(MeshAccessConnection::ConnectAsMaster(&bestCluster->addr, 10, 10, FmKeyId::NETWORK, nullptr, MeshAccessTunnelType::PEER_TO_PEER));
            //If a connection wasn't possible to establish
            if (!emergencyDisconnectValidationConnectionUniqueId.IsValid())
            {
                //We reset all the emergency disconnect values and try again after emergencyDisconnectTimerTriggerDs
                ResetEmergencyDisconnect();
                GS->logger.LogCustomError(CustomErrorTypes::WARN_COULD_NOT_CREATE_EMERGENCY_DISCONNECT_VALIDATION_CONNECTION, bestCluster->payload.clusterId);
            }
        }
        else if (emergencyDisconnectTimerDs >= emergencyDisconnectTimerTriggerDs)
        {
            if (emergencyDisconnectValidationConnectionUniqueId)
            {
                if (emergencyDisconnectValidationConnectionUniqueId.GetConnectionState() == ConnectionState::HANDSHAKE_DONE)
                {
                    SendModuleActionMessage(
                        MessageType::MODULE_TRIGGER_ACTION,
                        emergencyDisconnectValidationConnectionUniqueId.GetVirtualPartnerId(),
                        (u8)NodeModuleTriggerActionMessages::EMERGENCY_DISCONNECT,
                        0,
                        nullptr,
                        0,
                        false
                    );
                }
            }
            else
            {
                ResetEmergencyDisconnect();
                //This can happen in very rare conditions where several nodes enter the emergency state at the same time
                //and report their emergency to the same node.
                GS->logger.LogCustomError(CustomErrorTypes::WARN_UNEXPECTED_REMOVAL_OF_EMERGENCY_DISCONNECT_VALIDATION_CONNECTION, 0);
            }
        }
    }
    else
    {
        ResetEmergencyDisconnect();
    }

    //Count the nodes that are a good choice for connecting
    //TODO: We could use this snippet to connect immediately after enought nodes were collected
//    u8 numGoodNodesInBuffer = 0;
//    for (int i = 0; i < joinMePacketBuffer->_numElements; i++)
//    {
//        joinMeBufferPacket* packet = (joinMeBufferPacket*) joinMePacketBuffer->PeekItemAt(i);
//        u32 score = CalculateClusterScoreAsMaster(packet);
//        if (score > 0){
//            numGoodNodesInBuffer++;
//        }
//    }
//
//    if(numGoodNodesInBuffer >= Config->numNodesForDecision) ...

    //Check if there is a good cluster but add a random delay 
    if(lastDecisionTimeDs + Conf::maxTimeUntilDecisionDs <= GS->appTimerDs)
    {
        DecisionStruct decision = DetermineBestClusterAvailable();

        if (decision.result == Node::DecisionResult::NO_NODES_FOUND && noNodesFoundCounter < 100){
            noNodesFoundCounter++;
        } else if (decision.result == Node::DecisionResult::CONNECT_AS_MASTER || decision.result == Node::DecisionResult::CONNECT_AS_SLAVE){
            noNodesFoundCounter = 0;
        }

        //Save the last decision time and add a random delay so that two nodes that connect to each other will not repeatedly do so at the same time
        lastDecisionTimeDs = GS->appTimerDs + (Utility::GetRandomInteger() % 2 == 0 ? 1 : 0);

        StatusReporterModule* statusMod = (StatusReporterModule*)GS->node.GetModuleById(ModuleId::STATUS_REPORTER_MODULE);
        if(statusMod != nullptr){
            statusMod->SendLiveReport(LiveReportTypes::DECISION_RESULT, 0, (u8)(decision.result), decision.preferredPartner);
        }
    }

    if((disconnectTimestampDs !=0 && GS->appTimerDs >= disconnectTimestampDs + SEC_TO_DS(TIME_BEFORE_DISCOVERY_MESSAGE_SENT_SEC))&& Conf::GetInstance().highDiscoveryTimeoutSec != 0){
        logt("NODE","High Discovery message being sent after disconnect");
        //Message is broadcasted when connnection is lost to change the state to High Discovery
            u8 discoveryState = (u8)DiscoveryState::HIGH;
            SendModuleActionMessage(
                MessageType::MODULE_TRIGGER_ACTION,
                NODE_ID_BROADCAST,
                (u8)NodeModuleTriggerActionMessages::SET_DISCOVERY,
                0,
                &discoveryState,
                1,
                false
            );

            disconnectTimestampDs = 0;
    }

    //Reboot if a time is set
    if(rebootTimeDs != 0 && rebootTimeDs < GS->appTimerDs){
        logt("NODE", "Resetting!");
        //Do not reboot in safe mode
        *GS->rebootMagicNumberPtr = REBOOT_MAGIC_NUMBER;

        GS->ramRetainStructPtr->crc32 = Utility::CalculateCrc32((u8*)GS->ramRetainStructPtr, sizeof(RamRetainStruct) - 4);
        if (GS->ramRetainStructPtr->rebootReason == RebootReason::DFU){
#ifdef SIM_ENABLED
            cherrySimInstance->currentNode->fakeDfuVersionArmed = true;
#endif
            FruityHal::FeedWatchdog();
        }

        //Disconnect all connections on purpose so that others know the reason and do not reestablish
        GS->cm.ForceDisconnectAllConnections(AppDisconnectReason::REBOOT);
        //We must wait for a short while until the disconnect was done
        FruityHal::DelayMs(500);
        
        FruityHal::SystemReset();
    }


    if (isSendingCapabilities) {
        timeSinceLastCapabilitySentDs += passedTimeDs;
        if (timeSinceLastCapabilitySentDs >= TIME_BETWEEN_CAPABILITY_SENDINGS_DS)
        {
            //Implemented as fixedDelay instead of fixedRate, thus setting the variable to 0 instead of subtracting TIME_BETWEEN_CAPABILITY_SENDINGS_DS
            timeSinceLastCapabilitySentDs = 0;

            alignas(u32) CapabilityEntryMessage messageEntry;
            CheckedMemset(&messageEntry, 0, sizeof(CapabilityEntryMessage));
            messageEntry.header.header.messageType = MessageType::CAPABILITY;
            messageEntry.header.header.receiver = NODE_ID_BROADCAST;    //TODO this SHOULD be NODE_ID_SHORTEST_SINK, however that currently does not reach node 0 in the runner. Bug?
            messageEntry.header.header.sender = configuration.nodeId;
            messageEntry.header.actionType = CapabilityActionType::ENTRY;
            messageEntry.index = capabilityRetrieverGlobal;
            messageEntry.entry = GetNextGlobalCapability();

            if (messageEntry.entry.type == CapabilityEntryType::INVALID)
            {
                alignas(u32) CapabilityEndMessage message;
                CheckedMemset(&message, 0, sizeof(CapabilityEndMessage));
                message.header.header = messageEntry.header.header;
                message.header.actionType = CapabilityActionType::END;
                message.amountOfCapabilities = capabilityRetrieverGlobal;
                GS->cm.SendMeshMessage(
                    (u8*)&message,
                    sizeof(CapabilityEndMessage));
            }
            else if (messageEntry.entry.type == CapabilityEntryType::NOT_READY)
            {
                // If the module wasn't ready yet, we immediately
                // retry it on the next TimerEventHandler call.
                timeSinceLastCapabilitySentDs = TIME_BETWEEN_CAPABILITY_SENDINGS_DS;
            }
            else
            {
                GS->cm.SendMeshMessage(
                    (u8*)&messageEntry,
                    sizeof(CapabilityEntryMessage));
            }
        }
    }

    /*************************/
    /***                   ***/
    /***   GENERATE_LOAD   ***/
    /***                   ***/
    /*************************/
    if (generateLoadMessagesLeft > 0)
    {
        generateLoadTimeSinceLastMessageDs += passedTimeDs;
        while (generateLoadTimeSinceLastMessageDs >= generateLoadTimeBetweenMessagesDs
            && generateLoadMessagesLeft > 0)
        {
            generateLoadTimeSinceLastMessageDs -= generateLoadTimeBetweenMessagesDs;
            generateLoadMessagesLeft--;

            DYNAMIC_ARRAY(payloadBuffer, generateLoadPayloadSize);
            CheckedMemset(payloadBuffer, generateLoadMagicNumber, generateLoadPayloadSize);

            // 新增：標記 priority（支援混合交錯模式和單一優先級模式）
            if (generateLoadWithPriorityFlag && generateLoadPayloadSize > 0) {
                u8 currentPriority = generateLoadPriority;

                // 混合交錯模式：智能演算法決定當前封包的優先級
                if (generateLoadMixedMode) {
                    u32 remainingHigh = generateLoadHighTarget - generateLoadHighSent;
                    u32 remainingLow = generateLoadLowTarget - generateLoadLowSent;

                    bool sendHigh = false;

                    if (remainingHigh > 0 && remainingLow > 0) {
                        // 智能交錯演算法：Token Bucket + Weighted Round-Robin
                        // 策略 1：使用 interleavingRatio 控制交錯比例
                        // 例如 ratio=3 表示每 4 個封包中 3 個 HIGH, 1 個 LOW (3:1)
                        u32 cycleLength = generateLoadInterleavingRatio + 1;
                        u32 position = generateLoadMixedCounter % cycleLength;

                        if (position < generateLoadInterleavingRatio) {
                            // 在 HIGH 的位置
                            sendHigh = true;
                        } else {
                            // 在 LOW 的位置
                            sendHigh = false;
                        }

                        // 策略 2：動態調整 - 如果某種封包快用完，優先發送剩餘多的
                        // 避免最後只剩一種封包而無法交錯
                        u32 totalRemaining = remainingHigh + remainingLow;
                        if (totalRemaining > 0) {
                            // 如果 HIGH 剩餘比例低於目標比例，強制發送 LOW
                            float highRatio = (float)remainingHigh / totalRemaining;
                            float targetHighRatio = (float)generateLoadInterleavingRatio / cycleLength;

                            if (highRatio < targetHighRatio * 0.5f && remainingLow > cycleLength) {
                                sendHigh = false; // 切換到 LOW 避免 HIGH 太早用完
                            } else if (highRatio > targetHighRatio * 1.5f && remainingHigh > cycleLength) {
                                sendHigh = true; // 切換到 HIGH 避免 LOW 太早用完
                            }
                        }

                        generateLoadMixedCounter++;
                    } else if (remainingHigh > 0) {
                        sendHigh = true;
                    } else {
                        sendHigh = false;
                    }

                    if (sendHigh && remainingHigh > 0) {
                        currentPriority = 1; // HIGH priority
                        generateLoadHighSent++;
                    } else if (remainingLow > 0) {
                        currentPriority = 3; // LOW priority
                        generateLoadLowSent++;
                    }
                }else {
                    // 單一優先級模式：根據設定的 priority 更新對應計數器
                    // 這樣 snd_prio 才能收集到正確的數據
                    if (currentPriority <= 1) { // HIGH or VITAL
                        generateLoadHighSent++;
                    } else { // MEDIUM or LOW
                        generateLoadLowSent++;
                    }
                }

                payloadBuffer[0] = generateLoadPriorityMarker | (currentPriority & 0x0F);
            }

            //new
            // if(GS->MultipleUnit!=0){
            if(GS->MultipleUnit==0){
            for(int i=0;i<int(GS->MultipleUnit);i++){
            SendModuleActionMessage(
                MessageType::MODULE_TRIGGER_ACTION,
                generateLoadTarget,
                (u8)NodeModuleTriggerActionMessages::GENERATE_LOAD_CHUNK,
                generateLoadRequestHandle,
                payloadBuffer,
                generateLoadPayloadSize,
                false
            );
            }                
            }
            else{
            SendModuleActionMessage(
                MessageType::MODULE_TRIGGER_ACTION,
                generateLoadTarget,
                (u8)NodeModuleTriggerActionMessages::GENERATE_LOAD_CHUNK,
                generateLoadRequestHandle,
                payloadBuffer,
                generateLoadPayloadSize,
                false
            );
            }
        }
    }

    // Handle Device off
    GS->deviceOff.TimerHandler(passedTimeDs);
}

void Node::KeepHighDiscoveryActive()
{
    //If discovery is turned off, we should not turn it on
    if (currentDiscoveryState == DiscoveryState::IDLE) return;

    //Reset the state in discovery high, if anything in the cluster configuration changed
    if(currentDiscoveryState == DiscoveryState::HIGH){
        currentStateTimeoutDs = SEC_TO_DS(Conf::GetInstance().highDiscoveryTimeoutSec);
    } else {
        ChangeState(DiscoveryState::HIGH);
    }
}

/*
 #########################################################################################################
 ### Helper functions
 #########################################################################################################
 */
#define ________________HELPERS___________________

//Generates a new ClusterId by using connectionLoss and the unique id of the node
ClusterId Node::GenerateClusterID(void) const
{
    //Combine connection loss and nodeId to generate a unique cluster id
    ClusterId newId = configuration.nodeId + ((this->connectionLossCounter + randomBootNumber) << 16);

    logt("NODE", "New cluster id generated %x", newId);
    return newId;
}

ClusterSize Node::GetClusterSize(void) const
{
    return this->clusterSize;
}

void Node::SetClusterSize(ClusterSize clusterSize)
{
    if (clusterSize < GS->node.configuration.numberOfEnrolledDevices || GS->node.configuration.numberOfEnrolledDevices <= 1)
    {
        ChangeState(DiscoveryState::HIGH);
    }
    else
    {
        clusterSizeChangeHandled = false;
        clusterSizeTransitionTimeoutDs = SEC_TO_DS((u32)Conf::GetInstance().clusterSizeDiscoveryChangeDelaySec);
    }
    this->clusterSize = clusterSize;
}

void Node::SetEnrolledNodes(u16 enrolledNodes, NodeId sender)
{
    if (enrolledNodes == GS->node.configuration.numberOfEnrolledDevices) return;
    GS->node.configuration.numberOfEnrolledDevices = enrolledNodes;
    GS->cm.SetEnrolledNodesReceived(sender);
}

void Node::SendEnrolledNodes(u16 enrolledNodes, NodeId destinationNode)
{
    SetEnrolledNodesMessage message;
    message.enrolledNodes = enrolledNodes;
    SendModuleActionMessage(
        MessageType::MODULE_TRIGGER_ACTION,
        destinationNode,
        (u8)NodeModuleTriggerActionMessages::SET_ENROLLED_NODES,
        0,
        (u8*)(&message),
        sizeof(message),
        false
    );
}

bool Node::GetKey(FmKeyId fmKeyId, u8* keyOut) const
{
    if(fmKeyId == FmKeyId::NODE){
        CheckedMemcpy(keyOut, RamConfig->GetNodeKey(), 16);
        return true;
    } else if(fmKeyId == FmKeyId::NETWORK){
        CheckedMemcpy(keyOut, GS->node.configuration.networkKey, 16);
        return true;
    } else if(fmKeyId == FmKeyId::ORGANIZATION){
        CheckedMemcpy(keyOut, GS->node.configuration.organizationKey, 16);
        return true;
    } else if (fmKeyId == FmKeyId::RESTRAINED) {
        RamConfig->GetRestrainedKey(keyOut);
        return true;
    } else if(fmKeyId >= FmKeyId::USER_DERIVED_START && fmKeyId <= FmKeyId::USER_DERIVED_END){
        //Construct some cleartext with the user id to construct the user key
        u8 cleartext[16];
        CheckedMemset(cleartext, 0x00, 16);
        CheckedMemcpy(cleartext, &fmKeyId, 4);

        Utility::Aes128BlockEncrypt(
                (Aes128Block*)cleartext,
                (Aes128Block*)GS->node.configuration.userBaseKey,
                (Aes128Block*)keyOut);

        return true;
    } else {
        return false;
    }
}

Module* Node::GetModuleById(ModuleId id) const
{
    for(u32 i=0; i<GS->amountOfModules; i++){
        if(GS->activeModules[i]->moduleId == id){
            return GS->activeModules[i];
        }
    }
    return nullptr;
}

Module* Node::GetModuleById(VendorModuleId id) const
{
    for(u32 i=0; i<GS->amountOfModules; i++){
        if(Utility::IsSameModuleId(GS->activeModules[i]->vendorModuleId, id)){
            return GS->activeModules[i];
        }
    }
    return nullptr;
}

void Node::PrintStatus(void) const
{
    const FruityHal::BleGapAddr addr = FruityHal::GetBleGapAddress();

    trace("**************" EOL);
    trace("Node %s (nodeId: %u) vers: %u, NodeKey: %02X:%02X:....:%02X:%02X" EOL EOL, RamConfig->GetSerialNumber(), configuration.nodeId, GS->config.GetFruityMeshVersion(),
            RamConfig->GetNodeKey()[0], RamConfig->GetNodeKey()[1], RamConfig->GetNodeKey()[14], RamConfig->GetNodeKey()[15]);
    
    u16 meshMinConnectionIntervalValue = Conf::GetInstance().meshMinConnectionInterval * 1.25;
    u16 meshMaxConnectionIntervalValue = Conf::GetInstance().meshMaxConnectionInterval * 1.25;
    u16 meshScanIntervalHighValue = Conf::GetInstance().meshScanIntervalHigh * 0.625;
    u16 meshScanWindowHighValue = Conf::GetInstance().meshScanWindowHigh * 0.625;
    u16 meshScanIntervalLowValue = Conf::GetInstance().meshScanIntervalLow * 0.625;
    u16 meshScanWindowLowValue = Conf::GetInstance().meshScanWindowLow * 0.625;
    u16 connectionEventValue = GS->connectionEventvalue * 1.25;
            
    trace("meshMinConnectionIntervalValue : %u ms" EOL, meshMinConnectionIntervalValue);
    trace("meshMaxConnectionIntervalValue : %u ms" EOL, meshMaxConnectionIntervalValue);
    trace("meshScanIntervalHighValue : %u ms" EOL, meshScanIntervalHighValue);
    trace("meshScanIntervalLowValue : %u ms" EOL, meshScanIntervalLowValue);
    trace("meshScanWindowHighValue : %u ms" EOL, meshScanWindowHighValue);
    trace("meshScanWindowLowValue : %u ms" EOL, meshScanWindowLowValue);
    trace("connectionEventValue : %u ms" EOL EOL, connectionEventValue);
     
    SetTerminalTitle();
    trace("Mesh clusterSize:%u, clusterId:%u, featureset: %s, boardid: %u" EOL, clusterSize, clusterId, FEATURESET_NAME, Boardconfig->boardType);
    trace("Enrolled %u: networkId:%u, deviceType:%u, NetKey %02X:%02X:....:%02X:%02X, UserBaseKey %02X:%02X:....:%02X:%02X" EOL,
            (u32)configuration.enrollmentState, configuration.networkId, (u32)GET_DEVICE_TYPE(),
            configuration.networkKey[0], configuration.networkKey[1], configuration.networkKey[14], configuration.networkKey[15],
            configuration.userBaseKey[0], configuration.userBaseKey[1], configuration.userBaseKey[14], configuration.userBaseKey[15]);
    trace("Addr:%02X:%02X:%02X:%02X:%02X:%02X, ConnLossCounter:%u, AckField:%u, State: %u" EOL EOL,
            addr.addr[5], addr.addr[4], addr.addr[3], addr.addr[2], addr.addr[1], addr.addr[0],
            connectionLossCounter, currentAckId, (u32)currentDiscoveryState);

    //Print connection info
    BaseConnections conns = GS->cm.GetBaseConnections(ConnectionDirection::INVALID);
    trace("CONNECTIONS %u (freeIn:%u, freeOut:%u, pendingPackets:%u" EOL, conns.count, GS->cm.freeMeshInConnections, GS->cm.freeMeshOutConnections, GS->cm.GetPendingPackets());
    for (u32 i = 0; i < conns.count; i++) {
        BaseConnection *conn = conns.handles[i].GetConnection();
        conn->PrintStatus();
    }
    trace("**************" EOL);
}

void Node::SetTerminalTitle() const
{
#if IS_ACTIVE(SET_TERMINAL_TITLE)
    //Change putty terminal title
    if(Conf::GetInstance().terminalMode == TerminalMode::PROMPT) trace("\033]0;Node %u (%s) ClusterSize:%d (%x), [%u, %u, %u, %u]\007",
            configuration.nodeId,
            RamConfig->serialNumber,
            GS->node.GetClusterSize(), clusterId,
            GS->cm->allConnections[0] != nullptr ? GS->cm.allConnections[0]->partnerId : 0,
            GS->cm->allConnections[1] != nullptr ? GS->cm.allConnections[1]->partnerId : 0,
            GS->cm->allConnections[2] != nullptr ? GS->cm.allConnections[2]->partnerId : 0,
            GS->cm->allConnections[3] != nullptr ? GS->cm.allConnections[3]->partnerId : 0);
#endif
}

CapabilityEntry Node::GetCapability(u32 index, bool firstCall)
{
    if (index == 0) 
    {
        CapabilityEntry retVal;
        CheckedMemset(&retVal, 0, sizeof(retVal));
        retVal.type = CapabilityEntryType::SOFTWARE;
        strcpy(retVal.manufacturer, "M-Way Solutions GmbH");
        strcpy(retVal.modelName   , "BlueRange Node");
        Utility::GetVersionStringFromInt(GS->config.GetFruityMeshVersion(), retVal.revision);
        return retVal;
    }
    else if (index == 1)
    {
        size_t nameLength = strlen(FEATURESET_NAME);
        if (FEATURESET_NAME[nameLength - 1] == 'h' && FEATURESET_NAME[nameLength - 2] == '.')
        {
            // On real hardware, the macro FEATURESET_NAME contains .h at the end.
            // We do not want to transmit that as it does not add any information.
            nameLength -= 2;
        }
        const size_t lengthToCopy = nameLength <= sizeof(CapabilityEntry::revision) ? nameLength : sizeof(CapabilityEntry::revision);

        CapabilityEntry retVal;
        CheckedMemset(&retVal, 0, sizeof(retVal));
        retVal.type = CapabilityEntryType::PROPERTY;
        strcpy(retVal.manufacturer, "M-Way Solutions GmbH");
        strcpy(retVal.modelName,    "Featureset");
        CheckedMemcpy(retVal.revision, FEATURESET_NAME, lengthToCopy);
        return retVal;
    }

    else if (index == 2)
    {
        CapabilityEntry retVal;
        CheckedMemset(&retVal, 0, sizeof(retVal));
        retVal.type = CapabilityEntryType::PROPERTY;
        strcpy(retVal.manufacturer, "M-Way Solutions GmbH");
        strcpy(retVal.modelName, "Board Id");
        if (GS->boardconf.configuration.boardName == nullptr)
        {
            snprintf(retVal.revision, sizeof(retVal.revision), "%s (%u)", "UNKNOWN", GS->boardconf.configuration.boardType);
        }
        else
        {
            snprintf(retVal.revision, sizeof(retVal.revision), "%s (%u)", GS->boardconf.configuration.boardName, GS->boardconf.configuration.boardType);
        }
        return retVal;
    }
    else
    {
        return Module::GetCapability(index, firstCall);
    }
}

CapabilityEntry Node::GetNextGlobalCapability()
{
    CapabilityEntry retVal;
    retVal.type = CapabilityEntryType::INVALID;
    if (!isSendingCapabilities)
    {
        SIMEXCEPTION(IllegalStateException);
        return retVal;
    }

    while (retVal.type == CapabilityEntryType::INVALID && capabilityRetrieverModuleIndex < GS->amountOfModules)
    {
        retVal = GS->activeModules[capabilityRetrieverModuleIndex]->GetCapability(capabilityRetrieverLocal, firstCallForCurrentCapabilityModule);
        firstCallForCurrentCapabilityModule = false;
        if (retVal.type == CapabilityEntryType::INVALID) 
        {
            capabilityRetrieverLocal = 0;
            capabilityRetrieverModuleIndex++;
            firstCallForCurrentCapabilityModule = true;
        }
        else if (retVal.type == CapabilityEntryType::NOT_READY)
        {
            //Do nothing, will retry again shortly.
        }
        else
        {
            capabilityRetrieverLocal++;
            capabilityRetrieverGlobal++;
        }
    }

    if (retVal.type == CapabilityEntryType::INVALID)
    {
        isSendingCapabilities = false;
        firstCallForCurrentCapabilityModule = false;
    }
    return retVal;
}

void Node::PrintBufferStatus(void) const
{
    //Print JOIN_ME buffer
    trace("JOIN_ME Buffer:" EOL);
    for (u32 i = 0; i < joinMePackets.size(); i++)
    {
        const joinMeBufferPacket* packet = &joinMePackets[i];
        trace("=> %d, clstId:%u, clstSize:%d, freeIn:%u, freeOut:%u, writeHndl:%u, ack:%u, rssi:%d, ageDs:%d", packet->payload.sender, packet->payload.clusterId, packet->payload.clusterSize, packet->payload.freeMeshInConnections, packet->payload.freeMeshOutConnections, packet->payload.meshWriteHandle, packet->payload.ackField, packet->rssi, GS->appTimerDs - packet->receivedTimeDs);
        if (packet->advType == FruityHal::BleGapAdvType::ADV_IND)
        trace(" ADV_IND" EOL);
        else if (packet->advType == FruityHal::BleGapAdvType::ADV_NONCONN_IND)
        trace(" NON_CONN" EOL);
        else
        trace(" OTHER" EOL);
    }

    trace("**************" EOL);
}


void Node::RecordStorageEventHandler(u16 recordId, RecordStorageResultCode resultCode, u32 userType, u8* userData, u16 userDataLength)
{
    //After a factory reset of the RecordStorage, we need to reset
    if (userType == (u32)NodeSaveActions::FACTORY_RESET)
    {
        Reboot(SEC_TO_DS(1), RebootReason::FACTORY_RESET);
    }
    else if (userType == (u32)NodeSaveActions::ADD_DYNAMIC_GROUP
        || userType == (u32)NodeSaveActions::REMOVE_DYNAMIC_GROUP
        || userType == (u32)NodeSaveActions::CLEAR_DYNAMIC_GROUPS)
    {
        DynamicGroupSaveData* dgsd = (DynamicGroupSaveData*)userData;
        SendGroupResponse(dgsd->receiver, (NodeModuleActionResponseMessages)userType, dgsd->requestHandle, dgsd->group, resultCode);
    }
}

ErrorType Node::UpdateConnectionInterval(u16 connectionHandle, u16 newIntervalMs)
{
    // Convert milliseconds to BLE connection interval units (1.25ms units)
    u16 intervalUnits = MSEC_TO_UNITS(newIntervalMs, CONFIG_UNIT_1_25_MS);
    
    // Set up connection parameters
    FruityHal::BleGapConnParams connParams;
    connParams.minConnInterval = intervalUnits;
    connParams.maxConnInterval = intervalUnits;
    connParams.slaveLatency = 0;
    connParams.connSupTimeout = MSEC_TO_UNITS(6000, CONFIG_UNIT_10_MS); // 6 second timeout
    
    // Call the HAL function to update connection parameters
    ErrorType err = FruityHal::BleGapConnectionParamsUpdate(connectionHandle, connParams);
    
    if (err == ErrorType::SUCCESS) {
        logt("NODE", "Connection interval update initiated for handle %u to %u ms", connectionHandle, newIntervalMs);
    } else {
        logt("NODE", "Connection interval update failed for handle %u, error: %u", connectionHandle, (u32)err);
    }
    
    return err;
}

// //CE CE windowsize setting new
// void Node::SetConnectionInterval(u16 minConnectionInterval, u16 maxConnectionInterval)
// {
//     const u16 minAllowedInterval = (u16)MSEC_TO_UNITS(7.5, CONFIG_UNIT_1_25_MS);  // 範例值（對應 BLE 的 7.5 ms）
//     const u16 maxAllowedInterval = (u16)MSEC_TO_UNITS(4000, CONFIG_UNIT_1_25_MS); // 範例值（對應 BLE 的 4 秒）
//     if (minConnectionInterval < minAllowedInterval || minConnectionInterval > maxAllowedInterval ||
//         maxConnectionInterval < minAllowedInterval || maxConnectionInterval > maxAllowedInterval ||
//         minConnectionInterval > maxConnectionInterval) {
//         // 處理無效值
//         trace("無效的連接間隔值！必須 7.5ms~4000ms " EOL);
//         return;
//     }
//     Conf::meshMinConnectionInterval = (u16)MSEC_TO_UNITS(minConnectionInterval, CONFIG_UNIT_1_25_MS);
//     Conf::meshMaxConnectionInterval = (u16)MSEC_TO_UNITS(maxConnectionInterval, CONFIG_UNIT_1_25_MS);
// }

// void Node::SetConnectionEvent(u16 connectionEvent)
// {
    
// }

// void Node::SetWindowSize(u16 scanInterval, u16 scanWindow)
// {
//     const u16 minAllowedInterval = (u16)MSEC_TO_UNITS(2.5, CONFIG_UNIT_0_625_MS);  // 範例值（對應 BLE 的 2.5 ms）
//     const u16 maxAllowedInterval = (u16)MSEC_TO_UNITS(4000, CONFIG_UNIT_0_625_MS); // 範例值（對應 BLE 的 4 秒）
//     if (scanInterval < minAllowedInterval || scanInterval > maxAllowedInterval ||
//         scanWindow < minAllowedInterval || scanWindow > maxAllowedInterval ||
//         scanInterval < scanWindow) {
//         // 處理無效值
//         trace("無效的掃描間隔值！必須 2.5ms~4000ms " EOL);
//         return;
//     }
//     Conf::meshScanIntervalHigh = (u16)MSEC_TO_UNITS(scanInterval, CONFIG_UNIT_0_625_MS);
//     Conf::meshScanIntervalLow = (u16)MSEC_TO_UNITS(scanInterval, CONFIG_UNIT_0_625_MS);
//     Conf::meshScanWindowHigh = (u16)MSEC_TO_UNITS(scanWindow, CONFIG_UNIT_0_625_MS);
//     Conf::meshScanWindowLow = (u16)MSEC_TO_UNITS(scanWindow, CONFIG_UNIT_0_625_MS);
// }
/*
 #########################################################################################################
 ### Terminal Methods
 #########################################################################################################
 */

#ifdef TERMINAL_ENABLED
TerminalCommandHandlerReturnType Node::TerminalCommandHandler(const char* commandArgs[], u8 commandArgsSize)
{
    //Reporter
    if (commandArgsSize >= 1 && TERMARGS(0, "reporter")) {
        if(TERMARGS(1, "delay")){
            delayReporter = (delayReporter == 1) ? 0 : 1;
        }
        if(TERMARGS(1, "switch")){
            switchReporter = (switchReporter == 1) ? 0 : 1;
        }        
    } 
    if (TERMARGS(0, "repeat_load")) {
        generate_load = 0;
    }       
    if (commandArgsSize >= 3 && TERMARGS(0, "repeat_load")) {
        generateLoadTarget = Utility::TerminalArgumentToNodeId(commandArgs[1]); //目標
        generateLoadPayloadSize = Utility::TerminalArgumentToNodeId(commandArgs[2]); //size
        generateLoadRequestHandle = 0; //new
        GS->MultipleUnit=Utility::TerminalArgumentToNodeId(commandArgs[3]); //單位
        for (int j = 1; j <= TOTAL_NODE_NUM; j++) // for (int j = 1; j < TOTAL_NODE_NUM; j++)
            {
                if (j != configuration.nodeId) { //new
                    SendModuleActionMessage(
                        MessageType::MODULE_TRIGGER_ACTION,
                        j,
                        (u8)NodeModuleTriggerActionMessages::SET_UNIT,
                        GS->MultipleUnit,
                        nullptr,
                        0,
                        false
                    );
                }
            }
        generate_load = 1;   
        return TerminalCommandHandlerReturnType::SUCCESS;        
    }        
    //new test 四個目前沒用到
    if (TERMARGS(0, "flag")) {
        flag = 1;
        //printf("已設置flag=1\n\n");
        trace("已設置flag=1\n\n");
        
    }
    if (commandArgsSize >= 1 && TERMARGS(0, "set")) {
        ssettime=Utility::TerminalArgumentToNodeId(commandArgs[1]); //時間
        
    }
    if (commandArgsSize >= 2 && TERMARGS(0, "adjust")) {
        adjust=Utility::TerminalArgumentToNodeId(commandArgs[1]); // 時間
        errorIndex=Utility::TerminalArgumentToNodeId(commandArgs[2]); // 誤差值
    }
    if (TERMARGS(0, "flag0")) {
        flag = 0;
        //printf("已設置flag=0\n\n");
        trace("已設置flag=0\n\n");
    }


    if (TERMARGS(0, "time")) {
        trace("UTC TIME = %u" EOL, GS->timeManager.GetUtcTime());
    }

    if (TERMARGS(0, "tern")) {
        BaseConnections conn = GS->cm.GetBaseConnections(ConnectionDirection::INVALID);
        for (u8 i = 0; i < conn.count; i++)
        {
            if (conn.handles[i]) {
                if (conn.handles[i].GetConnectionState() == ConnectionState::DISABLED) {
                    conn.handles[i].HANDSHAKE_DONE();
                    //printf("\nhandle%u state%u count%d\n", (u8)conn.handles[i].GetConnectionHandle(), (u8)conn.handles[i].GetConnectionState(), counta);
                }

            }
        }
    }
    //React on commands, return true if handled, false otherwise
    if(commandArgsSize >= 3 && TERMARGS(2 , "node"))
    {
        if(TERMARGS(0 ,"action"))
        {
            //Rewrite "this" to our own node id, this will actually build the packet
            //But reroute it to our own node
            const NodeId destinationNode = Utility::TerminalArgumentToNodeId(commandArgs[1]);

            // //CE CE windowsize setting new
            // if (TERMARGS(3, "setci") && commandArgsSize >= 5)
            // {
            //     u16 minConnectionInterval = Utility::StringToU16(commandArgs[4]);
            //     u16 maxConnectionInterval = Utility::StringToU16(commandArgs[5]);
            //     SetConnectionInterval(minConnectionInterval, maxConnectionInterval);
            //     return TerminalCommandHandlerReturnType::SUCCESS;
            // }
            //new test
            if (TERMARGS(3, "flag")) 
            {
                flag=1;
                root = destinationNode; //將root設為目標node
                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    (u8)NodeModuleTriggerActionMessages::SET_FLAG,
                    0,
                    nullptr,
                    0,
                    false
                ); //發送一個SET_FLAG行動的封包給目標node
                   
                return TerminalCommandHandlerReturnType::SUCCESS;
            }            
            if (TERMARGS(3, "finddeg")) 
            {
                root = destinationNode; //將root設為目標node
                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    (u8)NodeModuleTriggerActionMessages::FIND_DEGREE,
                    0,
                    nullptr,
                    0,
                    false
                ); //發送一個FIND_DEGREE行動的封包給目標node
                   
                return TerminalCommandHandlerReturnType::SUCCESS;
            }
            if (TERMARGS(3, "setconsw")) //目前沒用
            {
                root = destinationNode; //將root設為目標node
                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    (u8)NodeModuleTriggerActionMessages::SET_CONSW,
                    0,
                    nullptr,
                    0,
                    false
                ); //發送一個setconsw行動的封包給目標node

                return TerminalCommandHandlerReturnType::SUCCESS;
            }
            if (TERMARGS(3, "init"))
            {
                root = destinationNode; //將root設為目標node
                trace("now root=%u\n\n", root);
                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    (u8)NodeModuleTriggerActionMessages::INIT_STATE,
                    0,
                    nullptr,
                    0,
                    false
                ); 
                return TerminalCommandHandlerReturnType::SUCCESS;
            }


            if (TERMARGS(3, "gettime") && commandArgsSize >= 4)
            {
                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    (u8)NodeModuleTriggerActionMessages::GET_TIME,
                    0,
                    nullptr,
                    0,
                    false
                );

                return TerminalCommandHandlerReturnType::SUCCESS;
            }

            if(commandArgsSize >= 5 && TERMARGS(3 ,"discovery"))
            {
                u8 discoveryState = (TERMARGS(4 , "idle")) ? 0 : 1;

                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    (u8)NodeModuleTriggerActionMessages::SET_DISCOVERY,
                    0,
                    &discoveryState,
                    1,
                    false
                );

                return TerminalCommandHandlerReturnType::SUCCESS;
            }
            //Send a reset command to a node in the mesh, it will then reboot
            if (commandArgsSize > 3 && TERMARGS(3, "reset"))
            {
                NodeModuleResetMessage data;
                data.resetSeconds = commandArgsSize > 4 ? Utility::StringToU8(commandArgs[4]) : 10;

                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    (u8)NodeModuleTriggerActionMessages::RESET_NODE,
                    0,
                    (u8*)&data,
                    SIZEOF_NODE_MODULE_RESET_MESSAGE,
                    false
                );

                return TerminalCommandHandlerReturnType::SUCCESS;
            }

            if (commandArgsSize > 3 && TERMARGS(3, "ping"))
            {
                const u8 requestHandle = commandArgsSize > 4 ? Utility::StringToU8(commandArgs[4]) : 0;
                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    (u8)NodeModuleTriggerActionMessages::PING,
                    requestHandle,
                    nullptr,
                    0,
                    false
                );

                return TerminalCommandHandlerReturnType::SUCCESS;
            }

            if (commandArgsSize > 7 && TERMARGS(3, "generate_load"))
            {
                //  0     1    2        3          4     5      6            7                 8
                //action this node generate_load target size repeats timeBetweenMessages {requestHandle}
                GenerateLoadTriggerMessage gltm;
                CheckedMemset(&gltm, 0, sizeof(GenerateLoadTriggerMessage));
                gltm.target                = Utility::StringToU16(commandArgs[4]);
                gltm.size                  = Utility::StringToU8 (commandArgs[5]);
                gltm.amount                = Utility::StringToU8 (commandArgs[6]);
                gltm.timeBetweenMessagesDs = Utility::StringToU8 (commandArgs[7]);

                const u8 requestHandle = commandArgsSize > 8 ? Utility::StringToU8(commandArgs[8]) : 0;
                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    (u8)NodeModuleTriggerActionMessages::START_GENERATE_LOAD,
                    requestHandle,
                    (u8*)&gltm,
                    sizeof(gltm),
                    false
                );

                return TerminalCommandHandlerReturnType::SUCCESS;
            }

            if (commandArgsSize > 4 && TERMARGS(3, "sync_multi_generate_load"))
            {
                //  0      1    2               3             4     5            6                  7            8          
                //action this node sync_multi_generate_load size repeats timeBetweenMessages {requestHandle} delayTime

                cmd[0] = commandArgs[0];
                cmd[1] = commandArgs[1];
                cmd[2] = commandArgs[2];
                cmd[3] = commandArgs[3];
                cmd[4] = commandArgs[4];
                cmd[5] = commandArgs[5];
                cmd[6] = commandArgs[6];
                cmd[7] = commandArgs[7];
                cmd[8] = commandArgs[8];

                ssettime = 30;
                delayTime = Utility::TerminalArgumentToNodeId(commandArgs[8]);;
                return TerminalCommandHandlerReturnType::SUCCESS;
            }

            //new command: let many nodes generate load
            if (commandArgsSize > 4 && TERMARGS(3, "multi_generate_load"))
            {
                //  0      1    2            3          4      5            6                  7
                //action this node multi_generate_load size repeats timeBetweenMessages {requestHandle}
                GenerateLoadTriggerMessage gltm;
                CheckedMemset(&gltm, 0, sizeof(GenerateLoadTriggerMessage));
                gltm.target = destinationNode;//TOTAL_NODE_NUM;//nnber
                gltm.size = Utility::StringToU8(commandArgs[4]);
                gltm.amount = Utility::StringToU16(commandArgs[5]);
                gltm.timeBetweenMessagesDs = Utility::StringToU8(commandArgs[6]);

                const u8 requestHandle = commandArgsSize > 8 ? Utility::StringToU8(commandArgs[7]) : 1; // new :0 update :1
                GS->MultipleUnit=requestHandle; //new
                GS->sndCount = gltm.amount * (TOTAL_NODE_NUM - 1)*requestHandle;
                //reset avg delay, PDR count
                GS->rcvCount = 0;
                for (int i = 0; i < TOTAL_NODE_NUM ; i++) //  for (int i = 0; i < TOTAL_NODE_NUM - 1; i++)
                {
                        MultipleCountArray[i]=0;
                        CollsndCountArray[i]=0;
                        avgDelay[i] = 0;
                        rcvCountArray[i] = 0;
                }

                // start generating for 1 sink only
                for (int j = 1; j <= TOTAL_NODE_NUM; j++) // for (int j = 1; j < TOTAL_NODE_NUM; j++)
                {
                    if (j != destinationNode) { //new
                        SendModuleActionMessage(
                            MessageType::MODULE_TRIGGER_ACTION,
                            j,
                            (u8)NodeModuleTriggerActionMessages::START_GENERATE_LOAD,
                            requestHandle,
                            (u8*)&gltm,
                            sizeof(gltm),
                            false
                        );
                    }
                }
                return TerminalCommandHandlerReturnType::SUCCESS;
            }
             // 新增命令：gen_load_mixed - 智能交錯傳輸 HIGH 和 LOW priority
            if (commandArgsSize > 7 && TERMARGS(3, "gen_load_mixed"))
            {
                // 0:action, 1:this, 2:node, 3:cmd, 4:size, 5:highAmt, 6:lowAmt, 7:interval, 8:requestHandle(opt), 9:ratio(opt)
                // 例如: action 1 node gen_load_mixed 30 150 50 1 1 3
                // 每個節點發送 150 HIGH + 50 LOW，requestHandle=1，交錯比例 3:1（每 4 個封包中 3 個 HIGH）

                GenerateLoadMixedMessage gltm;
                CheckedMemset(&gltm, 0, sizeof(GenerateLoadMixedMessage));

                // 1. 基本參數設定
                gltm.target = destinationNode;
                gltm.size = Utility::StringToU8(commandArgs[4]);
                gltm.highAmount = Utility::StringToU16(commandArgs[5]);
                gltm.lowAmount = Utility::StringToU16(commandArgs[6]);
                gltm.timeBetweenMessagesDs = Utility::StringToU8(commandArgs[7]);

                // 2. 讀取 requestHandle（可選參數，預設 1），支援 0-255
                const u8 requestHandle = commandArgsSize > 8 ? Utility::StringToU8(commandArgs[8]) : 1;

                // 3. 讀取交錯比例（可選參數，預設 3 表示 3:1）
                gltm.interleavingRatio = commandArgsSize > 9 ? Utility::StringToU8(commandArgs[9]) : 3;
                if (gltm.interleavingRatio == 0) gltm.interleavingRatio = 3;

                // 4. 直接將 requestHandle 存入結構體（支援 0-255）
                gltm.requestHandle = requestHandle;

                // 5. 統計設定
                GS->MultipleUnit = requestHandle;
                GS->sndCount = (gltm.highAmount + gltm.lowAmount) * (TOTAL_NODE_NUM - 1) * requestHandle;
                GS->rcvCount = 0;


                // 重置本地實際發送計數（包含重傳）
                generateLoadHighActualSent = 0;
                generateLoadLowActualSent = 0;

                // 重置所有統計陣列
                for (int i = 0; i < TOTAL_NODE_NUM; i++) {
                    MultipleCountArray[i] = 0;
                    CollsndCountArray[i] = 0;
                    avgDelay[i] = 0;
                    rcvCountArray[i] = 0;
                    avgDelayHighPrio[i] = 0;
                    avgDelayLowPrio[i] = 0;
                    rcvCountHighPrio[i] = 0;
                    rcvCountLowPrio[i] = 0;
                    sndCountHighPrio[i] = 0;
                    sndCountLowPrio[i] = 0;
                }

                // 直接使用 ratio 显示
                trace("Starting MIXED interleaved load: HIGH=%u, LOW=%u, ratio=%u:1, multiplier=%u" EOL,
                    gltm.highAmount, gltm.lowAmount, gltm.interleavingRatio, requestHandle);

                // 5. 發送命令給所有節點
                // 注意：使用 0xFD 作為特殊標記來識別混合交錯模式，避免與優先級值混淆
                for (int j = 1; j <= TOTAL_NODE_NUM; j++)
                {
                    if (j != destinationNode) {
                        SendModuleActionMessage(
                            MessageType::MODULE_TRIGGER_ACTION,
                            j,
                            (u8)NodeModuleTriggerActionMessages::START_GENERATE_LOAD,
                            0xFD, // 特殊標記：混合交錯模式（避免與 DeliveryPriority 衝突）
                            (u8*)&gltm,
                            sizeof(gltm),
                            false
                        );
                    }
                }
                return TerminalCommandHandlerReturnType::SUCCESS;
            }

             // 新增命令：支持指定優先級的多節點負載生成
            if (commandArgsSize > 7 && TERMARGS(3, "gen_load_prio"))
            {
                // 0:action, 1:this, 2:node, 3:cmd, 4:size, 5:amt, 6:interval, 7:priority, 8:handle(opt)

                GenerateLoadWithPriorityMessage gltm;
                CheckedMemset(&gltm, 0, sizeof(GenerateLoadWithPriorityMessage));

                // 1. 基本參數設定
                gltm.target = destinationNode;
                gltm.size = Utility::StringToU8(commandArgs[4]);
                gltm.amount = Utility::StringToU16(commandArgs[5]);
                gltm.timeBetweenMessagesDs = Utility::StringToU8(commandArgs[6]);

                // 2. 讀取優先級參數
                // 假設輸入 1 代表 High Priority，3 代表 Low Priority
                u8 priorityVal = Utility::StringToU8(commandArgs[7]);
                gltm.priority = priorityVal;

                // 3. 處理 Handle (因為多插了一個參數，所以 Handle 變成第 9 個參數，index 8)
                const u8 requestHandle = commandArgsSize > 8 ? Utility::StringToU8(commandArgs[8]) : 1;

                // 4. 統計設定
                GS->MultipleUnit = requestHandle;
                GS->sndCount = gltm.amount * (TOTAL_NODE_NUM - 1) * requestHandle;
                GS->rcvCount = 0;

                 // 重置本地實際發送計數（包含重傳）
                generateLoadHighActualSent = 0;
                generateLoadLowActualSent = 0;

                // 重置接收端統計陣列（包括 priority 統計）
                for (int i = 0; i < TOTAL_NODE_NUM; i++) {
                    MultipleCountArray[i] = 0;
                    CollsndCountArray[i] = 0;
                    avgDelay[i] = 0;
                    rcvCountArray[i] = 0;
                    avgDelayHighPrio[i] = 0;
                    avgDelayLowPrio[i] = 0;
                    rcvCountHighPrio[i] = 0;
                    rcvCountLowPrio[i] = 0;
                    sndCountHighPrio[i] = 0;
                    sndCountLowPrio[i] = 0;
                }

                // 5. 發送命令給所有節點
                for (int j = 1; j <= TOTAL_NODE_NUM; j++)
                {
                    if (j != destinationNode) {
                        SendModuleActionMessage(
                            MessageType::MODULE_TRIGGER_ACTION,
                            j,
                            (u8)NodeModuleTriggerActionMessages::START_GENERATE_LOAD,
                            requestHandle,
                            (u8*)&gltm,
                            sizeof(gltm),
                            false
                        );
                    }
                }
                return TerminalCommandHandlerReturnType::SUCCESS;
            }

            //new command: coll sndCount
            if (commandArgsSize >3 && TERMARGS(3, "snd"))
            {   GS->CollsndCount=0;
                GS->MultipleCount=0;
                // COLLECT_TRANSMIT_DATA
                for (int j = 1; j <= TOTAL_NODE_NUM; j++) 
                {
                    if (j != destinationNode) { //new
                        SendModuleActionMessage(
                            MessageType::MODULE_TRIGGER_ACTION,
                            j,
                            (u8)NodeModuleTriggerActionMessages::COLLECT_TRANSMIT_DATA,
                            0,
                            nullptr,
                            0,
                            false
                        );
                    }
                }
                return TerminalCommandHandlerReturnType::SUCCESS;                
            }

             //新增命令: 收集混合模式的统计数据
            if (commandArgsSize > 3 && TERMARGS(3, "snd_mixed"))
            {
                trace("Collecting MIXED mode statistics..." EOL);

                // 发送收集命令给所有节点
                for (int j = 1; j <= TOTAL_NODE_NUM; j++) 
                {
                    if (j != destinationNode) {
                        SendModuleActionMessage(
                            MessageType::MODULE_TRIGGER_ACTION,
                            j,
                            (u8)NodeModuleTriggerActionMessages::COLLECT_MIXED_DATA,
                            0,
                            nullptr,
                            0,
                            false
                        );
                    }
                }

                trace("MIXED mode statistics collection sent" EOL);
                return TerminalCommandHandlerReturnType::SUCCESS;
            }

            //新增命令: 收集 priority 分开的统计数据
            if (commandArgsSize > 3 && TERMARGS(3, "snd_prio"))
            {
                // 发送收集命令给所有节点
                for (int j = 1; j <= TOTAL_NODE_NUM; j++) 
                {
                    if (j != destinationNode) {
                        SendModuleActionMessage(
                            MessageType::MODULE_TRIGGER_ACTION,
                            j,
                            (u8)NodeModuleTriggerActionMessages::COLLECT_MIXED_DATA,
                            0,
                            nullptr,
                            0,
                            false
                        );
                    }
                }

                trace("Collecting priority statistics from all nodes" EOL);
                return TerminalCommandHandlerReturnType::SUCCESS;
            }

            //新增命令: 重置 priority 统计数据
            if (commandArgsSize > 3 && TERMARGS(3, "reset_prio"))
            {
                // 重置所有 priority 统计
                for (int i = 0; i < TOTAL_NODE_NUM; i++) {
                    avgDelayHighPrio[i] = 0;
                    avgDelayLowPrio[i] = 0;
                    rcvCountHighPrio[i] = 0;
                    rcvCountLowPrio[i] = 0;
                }

                trace("Priority statistics reset" EOL);
                return TerminalCommandHandlerReturnType::SUCCESS;
            }

            //new command: avg delay result
            if (commandArgsSize > 3 && TERMARGS(3, "result"))
            {                
                //  0     1    2      3
                //action this node result
                u32 avg = 0;
                GS->rcvCount = 0;
                for (int i = 0; i < TOTAL_NODE_NUM; i++)
                {
                    if ((i+1) != destinationNode) { //new
                        u32 temp;
                        u32 sendcount=0;
                        sendcount = (CollsndCountArray[i]+(GS->MultipleUnit*MultipleCountArray[i]));
                        if (rcvCountArray[i] == 0)
                            temp = 0;
                        else
                            temp = avgDelay[i] / rcvCountArray[i];
                        trace("Avg delay of node %d = %u ms , send count = %u , rcv count = %d " EOL, i + 1, temp, sendcount, rcvCountArray[i]);
                        avg += temp;

                        GS->rcvCount += rcvCountArray[i];
                    }
                }

                //printf("Avg delay of all nodes = %u ms\n", avg / (TOTAL_NODE_NUM - 1));
                //printf("send count = %u, rcv count = %u\n", GS->sndCount, GS->rcvCount);
               // trace("Avg delay of all nodes = %u ms" EOL,  avg / (TOTAL_NODE_NUM - 1));
                trace("MultipleCount : %u , MultipleUnit : %u , CollsndCount : %u ," EOL, GS->MultipleCount, GS->MultipleUnit, GS->CollsndCount);
                trace("Avg delay of all nodes = %u ms" EOL,  avg / (TOTAL_NODE_NUM - 1));
                trace("COL send count = %u, send count = %u, rcv count = %u" EOL, GS->CollsndCount+(GS->MultipleUnit*GS->MultipleCount), GS->sndCount, GS->rcvCount);
                GS->rcvCount=0;
                for (int i = 0; i < TOTAL_NODE_NUM ; i++) //  for (int i = 0; i < TOTAL_NODE_NUM - 1; i++)
                {
                        MultipleCountArray[i]=0;
                        CollsndCountArray[i]=0;
                        avgDelay[i] = 0;
                        rcvCountArray[i] = 0;
                }
                return TerminalCommandHandlerReturnType::SUCCESS;
            }
             //新增命令: 统计高和低優先權封包同時傳送结果
            if (commandArgsSize > 3 && TERMARGS(3, "result_mixed"))
            {
                trace("\\n========== Priority Statistics (Accurate with Retransmission Tracking) ==========" EOL);
                trace("NOTE: snd counts now include retransmissions tracked at connection layer!" EOL);

                u32 avgHigh = 0, avgLow = 0;
                u32 totalHighRcv = 0, totalLowRcv = 0;
                u32 totalHighSnd = 0, totalLowSnd = 0;

                for (int i = 0; i < TOTAL_NODE_NUM; i++)
                {
                    if ((i+1) != destinationNode) {
                        u32 tempHigh = 0, tempLow = 0;

                        // 直接使用連接層統計的實際發送數（包含重傳）
                        // 這是準確的！因為每次發送時都檢查 payload 的 priority
                        u32 highSendCount = sndCountHighPrio[i];
                        u32 lowSendCount = sndCountLowPrio[i];

                        if (rcvCountHighPrio[i] > 0) {
                            tempHigh = avgDelayHighPrio[i] / rcvCountHighPrio[i];
                            avgHigh += tempHigh;
                            totalHighRcv += rcvCountHighPrio[i];
                        }

                        if (rcvCountLowPrio[i] > 0) {
                            tempLow = avgDelayLowPrio[i] / rcvCountLowPrio[i];
                            avgLow += tempLow;
                            totalLowRcv += rcvCountLowPrio[i];
                        }

                        totalHighSnd += highSendCount;
                        totalLowSnd += lowSendCount;

                        trace("Node %d: HIGH=%u ms (snd=%u, rcv=%u), LOW=%u ms (snd=%u, rcv=%u)" EOL, 
                            i + 1, 
                            tempHigh, highSendCount, rcvCountHighPrio[i],
                            tempLow, lowSendCount, rcvCountLowPrio[i]);
                    }
                }

                u32 activeNodes = TOTAL_NODE_NUM - 1;
                if (activeNodes > 0) {
                    trace("\\nOverall: HIGH=%u ms (snd=%u, rcv=%u), LOW=%u ms (snd=%u, rcv=%u)" EOL,
                        totalHighRcv > 0 ? avgHigh / activeNodes : 0, totalHighSnd, totalHighRcv,
                        totalLowRcv > 0 ? avgLow / activeNodes : 0, totalLowSnd, totalLowRcv);

                    if (totalHighRcv > 0 && totalLowRcv > 0) {
                        u32 avgHighDelay = avgHigh / activeNodes;
                        u32 avgLowDelay = avgLow / activeNodes;
                        if (avgHighDelay < avgLowDelay) {
                            u32 improvement = ((avgLowDelay - avgHighDelay) * 100) / avgLowDelay;
                            trace("HIGH priority is %u%% faster than LOW" EOL, improvement);
                        }
                    }

                    // 显示发送统计
                    u32 expectedTotal = GS->sndCount;
                    u32 actualTotal = totalHighSnd + totalLowSnd;
                    trace("Expected total: %u, Actual total: %u (HIGH=%u, LOW=%u)" EOL,
                        expectedTotal, actualTotal, totalHighSnd, totalLowSnd);
                }
                trace("===============================================================================" EOL);

                return TerminalCommandHandlerReturnType::SUCCESS;
            }

            //新增命令: 显示 priority 分开的统计结果
            if (commandArgsSize > 3 && TERMARGS(3, "result_prio"))
            {
                trace("\\n========== Priority Statistics ==========" EOL);

                u32 avgHigh = 0, avgLow = 0;
                u32 totalHighRcv = 0, totalLowRcv = 0;
                u32 totalHighSnd = 0, totalLowSnd = 0;

                for (int i = 0; i < TOTAL_NODE_NUM; i++)
                {
                    if ((i+1) != destinationNode) {
                        u32 tempHigh = 0, tempLow = 0;

                        // 获取目标发送数（不含重传）
                        u32 highTargetCount = sndCountHighPrio[i];
                        u32 lowTargetCount = sndCountLowPrio[i];
                        u32 totalTargetCount = highTargetCount + lowTargetCount;

                        // 计算实际发送数（包含重传），使用和 result 相同的公式
                        u32 actualTotalSend = (CollsndCountArray[i] + (GS->MultipleUnit * MultipleCountArray[i]));

                        // 按比例分配实际发送数到 HIGH 和 LOW
                        // 先算 HIGH，然后 LOW = 总数 - HIGH，避免舍入误差
                        u32 highSendCount = 0;
                        u32 lowSendCount = 0;
                        if (totalTargetCount > 0) {
                            highSendCount = (actualTotalSend * highTargetCount) / totalTargetCount;
                            lowSendCount = actualTotalSend - highSendCount;  // 用减法避免舍入误差
                        }
                        if (rcvCountHighPrio[i] > 0) {
                            tempHigh = avgDelayHighPrio[i] / rcvCountHighPrio[i];
                            avgHigh += tempHigh;
                            totalHighRcv += rcvCountHighPrio[i];
                        }

                        if (rcvCountLowPrio[i] > 0) {
                            tempLow = avgDelayLowPrio[i] / rcvCountLowPrio[i];
                            avgLow += tempLow;
                            totalLowRcv += rcvCountLowPrio[i];
                        }

                        totalHighSnd += highSendCount;
                        totalLowSnd += lowSendCount;

                        trace("Node %d: HIGH=%u ms (rcv=%u), LOW=%u ms (rcv=%u)" EOL, 
                            i + 1, 
                            tempHigh, rcvCountHighPrio[i],
                            tempLow, rcvCountLowPrio[i]);
                    }
                }

                u32 activeNodes = TOTAL_NODE_NUM - 1;
                if (activeNodes > 0) {
                    // 计算整体重传统计
                    u32 totalHighRetrans = (totalHighSnd > totalHighRcv) ? (totalHighSnd - totalHighRcv) : 0;
                    u32 totalLowRetrans = (totalLowSnd > totalLowRcv) ? (totalLowSnd - totalLowRcv) : 0;
                    u32 overallHighRetransRate = (totalHighRcv > 0) ? ((totalHighRetrans * 100) / totalHighRcv) : 0;
                    u32 overallLowRetransRate = (totalLowRcv > 0) ? ((totalLowRetrans * 100) / totalLowRcv) : 0;

                    trace("\\nOverall: HIGH=%u ms (rcv=%u), LOW=%u ms (rcv=%u)" EOL,
                        totalHighRcv > 0 ? avgHigh / activeNodes : 0, totalHighRcv,
                        totalLowRcv > 0 ? avgLow / activeNodes : 0, totalLowRcv);

                    if (totalHighRcv > 0 && totalLowRcv > 0) {
                        u32 avgHighDelay = avgHigh / activeNodes;
                        u32 avgLowDelay = avgLow / activeNodes;
                        if (avgHighDelay < avgLowDelay) {
                            u32 improvement = ((avgLowDelay - avgHighDelay) * 100) / avgLowDelay;
                            trace("HIGH priority is %u%% faster" EOL, improvement);
                        }
                    }

                    // 显示发送统计
                    u32 expectedTotal = GS->sndCount;
                    u32 actualTotal = totalHighSnd + totalLowSnd;
                }
                trace("=========================================" EOL);

                return TerminalCommandHandlerReturnType::SUCCESS;
            }


            if (
                   commandArgsSize >= 5 
                && commandArgsSize <= 5 + Conf::MAX_AMOUNT_PREFERRED_PARTNER_IDS 
                && TERMARGS(3, "set_preferred_connections")
                )
            {
                PreferredConnectionMessage message;
                if (TERMARGS(4, "ignored"))
                {
                    message.preferredConnectionMode = PreferredConnectionMode::IGNORED;
                }
                else if (TERMARGS(4, "penalty"))
                {
                    message.preferredConnectionMode = PreferredConnectionMode::PENALTY;
                }
                else
                {
                    SIMEXCEPTION(IllegalArgumentException); //LCOV_EXCL_LINE assertion
                    return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;
                }
                message.preferredConnectionMode = (TERMARGS(4, "ignored")) ? PreferredConnectionMode::IGNORED : PreferredConnectionMode::PENALTY;
                message.amountOfPreferredPartnerIds = commandArgsSize - 5;

                if (message.amountOfPreferredPartnerIds > Conf::MAX_AMOUNT_PREFERRED_PARTNER_IDS) 
                {
                    SIMEXCEPTION(IllegalArgumentException);
                    return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;
                }

                bool didError = false;
                for (size_t i = 0; i < message.amountOfPreferredPartnerIds; i++)
                {
                    message.preferredPartnerIds[i] = Utility::StringToU16(commandArgs[5 + i], &didError);
                }

                if (didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    (u8)NodeModuleTriggerActionMessages::SET_PREFERRED_CONNECTIONS,
                    0,
                    (u8*)&message,
                    sizeof(PreferredConnectionMessage),
                    false
                );

                return TerminalCommandHandlerReturnType::SUCCESS;
            }
            
            if(commandArgsSize >= 5 && TERMARGS(3 ,"set_enrolled_nodes"))
            {
                bool didError = false;
                const u16 enrolledNodes = Utility::StringToU32(commandArgs[4], &didError);
                if ((enrolledNodes > 2000) || didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

                SetEnrolledNodesMessage message;
                message.enrolledNodes = enrolledNodes;
                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    (u8)NodeModuleTriggerActionMessages::SET_ENROLLED_NODES,
                    0,
                    (u8*)(&message),
                    sizeof(message),
                    false
                );

                return TerminalCommandHandlerReturnType::SUCCESS;
            }

            if (TERMARGS(3, "add_group") || TERMARGS(3, "remove_group"))
            {
                if (commandArgsSize < 5) return TerminalCommandHandlerReturnType::NOT_ENOUGH_ARGUMENTS;
                bool didError = false;
                const NodeId dynamicGroup = Utility::TerminalArgumentToNodeId(commandArgs[4], &didError);
                const u8 requestHandle = commandArgsSize > 5 ? Utility::StringToU8(commandArgs[5], &didError) : 0;
                if (didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

                u8 actionType = 0;
                if (TERMARGS(3, "add_group"))
                {
                    actionType = (u8)NodeModuleTriggerActionMessages::ADD_DYNAMIC_GROUP;
                }
                else if (TERMARGS(3, "remove_group"))
                {
                    actionType = (u8)NodeModuleTriggerActionMessages::REMOVE_DYNAMIC_GROUP;
                }
                else
                {
                    // Implementation bug!
                    SIMEXCEPTION(IllegalStateException);
                    return TerminalCommandHandlerReturnType::INTERNAL_ERROR;
                }

                AddOrRemoveDynamicGroupMessage message;
                message.id = dynamicGroup;

                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    actionType,
                    requestHandle,
                    (u8*)(&message),
                    sizeof(message),
                    false
                );

                return TerminalCommandHandlerReturnType::SUCCESS;
            }

            if (TERMARGS(3, "clear_groups"))
            {
                bool didError = false;
                const u8 requestHandle = commandArgsSize > 4 ? Utility::StringToU8(commandArgs[4], &didError) : 0;
                if (didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    (u8)NodeModuleTriggerActionMessages::CLEAR_DYNAMIC_GROUPS,
                    requestHandle,
                    nullptr,
                    0,
                    false
                );

                return TerminalCommandHandlerReturnType::SUCCESS;
            }

            if (TERMARGS(3, "get_groups"))
            {
                bool didError = false;
                const u8 requestHandle = commandArgsSize > 4 ? Utility::StringToU8(commandArgs[4], &didError) : 0;
                if (didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

                SendModuleActionMessage(
                    MessageType::MODULE_TRIGGER_ACTION,
                    destinationNode,
                    (u8)NodeModuleTriggerActionMessages::GET_DYNAMIC_GROUPS,
                    requestHandle,
                    nullptr,
                    0,
                    false
                );

                return TerminalCommandHandlerReturnType::SUCCESS;
            }

         //新加入動態調整CI方法
            else if (TERMARGS(3, "set_scan_interval"))
            {
                if (commandArgsSize < 5) return TerminalCommandHandlerReturnType::NOT_ENOUGH_ARGUMENTS;
                bool didError = false;
                u16 interval = Utility::StringToU16(commandArgs[4], &didError);
                if (didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

                NodeId targetNodeId = 0;
                if (commandArgsSize >= 6) {
                    targetNodeId = Utility::TerminalArgumentToNodeId(commandArgs[5], &didError);
                    if (didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;
                }

                if (targetNodeId != 0) {
                    logt("CMD", "Requesting connection interval to be updated to %u ms for node %u's connection with peer %u (using set_scan_interval command).", interval, destinationNode, targetNodeId);

                    struct UpdateConnIntervalMessageWithTarget {
                        u16 newIntervalMs;
                        NodeId targetNodeId;
                    };

                    UpdateConnIntervalMessageWithTarget message;
                    message.newIntervalMs = interval;
                    message.targetNodeId = targetNodeId;

                    SendModuleActionMessage(
                        MessageType::MODULE_TRIGGER_ACTION, destinationNode,
                        (u8)NodeModuleTriggerActionMessages::SET_CONN_INTERVAL,
                        0, (u8*)&message, sizeof(message), false);
                } else {
                    logt("CMD", "Requesting scan interval to be updated to %u ms for node %u.", interval, destinationNode);

                    UpdateConnIntervalMessage message;
                    message.newIntervalMs = interval;

                    SendModuleActionMessage(
                        MessageType::MODULE_TRIGGER_ACTION, destinationNode,
                        (u8)NodeModuleTriggerActionMessages::SET_SCAN_INTERVAL,
                        0, (u8*)&message, sizeof(message), false);
                }

                return TerminalCommandHandlerReturnType::SUCCESS;
            }
            else if (TERMARGS(3, "set_conn_interval"))
            {
                if (commandArgsSize < 5) return TerminalCommandHandlerReturnType::NOT_ENOUGH_ARGUMENTS;
                bool didError = false;
                u16 interval = Utility::StringToU16(commandArgs[4], &didError);
                if (didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

                NodeId targetNodeId = 0;
                if (commandArgsSize >= 6) {
                    targetNodeId = Utility::TerminalArgumentToNodeId(commandArgs[5], &didError);
                    if (didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;
                }

                if (targetNodeId != 0) {
                    logt("CMD", "Requesting connection interval to be updated to %u ms for node %u's connection with peer %u.", interval, destinationNode, targetNodeId);

                    struct UpdateConnIntervalMessageWithTarget {
                        u16 newIntervalMs;
                        NodeId targetNodeId;
                    };

                    UpdateConnIntervalMessageWithTarget message;
                    message.newIntervalMs = interval;
                    message.targetNodeId = targetNodeId;

                    SendModuleActionMessage(
                        MessageType::MODULE_TRIGGER_ACTION, destinationNode,
                        (u8)NodeModuleTriggerActionMessages::SET_CONN_INTERVAL,
                        0, (u8*)&message, sizeof(message), false);
                } else {
                    logt("CMD", "Requesting connection interval to be updated to %u ms for node %u.", interval, destinationNode);

                    UpdateConnIntervalMessage message;
                    message.newIntervalMs = interval;

                    SendModuleActionMessage(
                        MessageType::MODULE_TRIGGER_ACTION, destinationNode,
                        (u8)NodeModuleTriggerActionMessages::SET_CONN_INTERVAL,
                        0, (u8*)&message, sizeof(message), false);
                }

                return TerminalCommandHandlerReturnType::SUCCESS;
            }  
        }
    }

    /************* SYSTEM ***************/
    if (TERMARGS(0 ,"reset"))
    {
        Reboot(1, RebootReason::LOCAL_RESET);
        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    /************* NODE ***************/
    //Get a full status of the node
    else if (TERMARGS(0, "status"))
    {
        PrintStatus();

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //Allows us to send arbitrary mesh packets (not to be confused with the raw data protocol)
    else if (TERMARGS(0, "rawsend") && commandArgsSize > 1) {
        DYNAMIC_ARRAY(buffer, 200);
        u32 len = Logger::ParseEncodedStringToBuffer(commandArgs[1], buffer, 200);

        //TODO: We could optionally allow to specify delivery priority and reliability

        GS->cm.SendMeshMessage(buffer, len);

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
#ifdef SIM_ENABLED
    //Allows us to send arbitrary mesh packets and queue them directly without other checks
    //MUST NOT BE USED EXCEPT FOR TESTING
    else if (TERMARGS(0, "rawsend_high") && commandArgsSize > 1) {
        DYNAMIC_ARRAY(buffer, 200);
        u32 len = Logger::ParseEncodedStringToBuffer(commandArgs[1], buffer, 200);

        //Because the implementation doesn't easily allow us to send WRITE_REQ to all connections, we have to work around that
        BaseConnections conns = GS->cm.GetBaseConnections(ConnectionDirection::INVALID);
        for (u32 i = 0; i < conns.count; i++)
        {
            BaseConnection* conn = conns.handles[i].GetConnection();
            if (!conn) continue;
            
            if (conn->connectionType == ConnectionType::FRUITYMESH) {
                MeshConnection* mconn = (MeshConnection*)conn;
                mconn->SendHandshakeMessage(buffer, len, true);
            }
            else if (conn->connectionType == ConnectionType::MESH_ACCESS) {
                MeshAccessConnection* mconn = (MeshAccessConnection*)conn;
                mconn->SendData(buffer, len, true);
            }
        }

        return TerminalCommandHandlerReturnType::SUCCESS;
    }

#endif //SIM_ENABLED

    // ################# Raw Data Protocol #######################
    //Sends a small packet that can have different protocol types
    //raw_data_light [receiverId] [destinationModule] [protocolId] [payload] {requestHandle = 0}
    else if (commandArgsSize >= 5 && TERMARGS(0, "raw_data_light"))
    {
        u8 buffer[MAX_MESH_PACKET_SIZE];
        CheckedMemset(&buffer, 0, sizeof(buffer));

        NodeId receiverId = Utility::TerminalArgumentToNodeId(commandArgs[1]);
        ModuleIdWrapper moduleId = Utility::GetWrappedModuleIdFromTerminal(commandArgs[2]);
        RawDataProtocol protocolId = static_cast<RawDataProtocol>(Utility::StringToU8(commandArgs[3]));

        bool didError = false;
        u16 payloadLength = Logger::ParseEncodedStringToBuffer(commandArgs[4], buffer, sizeof(buffer), &didError);
        if(didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

        u8 requestHandle = commandArgsSize >= 6 ? Utility::StringToU8(commandArgs[5]) : 0;


        GS->cm.SendModuleActionMessage(
            MessageType::MODULE_RAW_DATA_LIGHT,
            moduleId,
            receiverId,
            (u8)protocolId,
            requestHandle,
            buffer,
            payloadLength,
            false,
            true
        );

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //Send some large data that is split over a few messages
    //raw_data_start [receiverId] [destinationModule] [numChunks] [protocolId] {requestHandle = 0} {metadataHex = ""}
    else if(commandArgsSize >= 5 && TERMARGS(0, "raw_data_start"))
    {
        u8 buffer[SIZEOF_RAW_DATA_START_PAYLOAD + MAX_RAW_DATA_METADATA_SIZE];
        CheckedMemset(buffer, 0, sizeof(buffer));

        bool didError = false;

        NodeId receiverId = Utility::TerminalArgumentToNodeId(commandArgs[1], &didError);
        ModuleIdWrapper moduleId = Utility::GetWrappedModuleIdFromTerminal(commandArgs[2], &didError);

        RawDataStartPayload* data = (RawDataStartPayload*)buffer;
        data->numChunks = Utility::StringToU32(commandArgs[3], &didError);
        data->protocolId = (u32)static_cast<RawDataProtocol>(Utility::StringToU8(commandArgs[4], &didError));
        data->fmKeyId = 0; //TODO: IOT-1465

        u8 requestHandle = commandArgsSize >= 6 ? Utility::StringToU8(commandArgs[5], &didError) : 0;

        u16 metadataLen = 0;
        if (commandArgsSize >= 7) {
            metadataLen = Logger::ParseEncodedStringToBuffer(commandArgs[6], data->metadata, MAX_RAW_DATA_METADATA_SIZE, &didError);
        }

        if (didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

        GS->cm.SendModuleActionMessage(
            MessageType::MODULE_RAW_DATA,
            moduleId,
            receiverId,
            (u8)RawDataActionType::START,
            requestHandle,
            (u8*)data,
            sizeof(RawDataStartPayload) + metadataLen,
            false,
            true
        );

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //raw_data_error [receiverId] [destinationModule] [errorCode] [destination] {requestHandle = 0}
    else if (commandArgsSize >= 5 && TERMARGS(0, "raw_data_error"))
    {
        bool didError = false;
        RawDataErrorPayload data;
        CheckedMemset(&data, 0x00, sizeof(data));

        NodeId receiverId = Utility::TerminalArgumentToNodeId(commandArgs[1], &didError);
        ModuleIdWrapper moduleId = Utility::GetWrappedModuleIdFromTerminal(commandArgs[2], &didError);

        data.error = (RawDataErrorType)Utility::StringToU8(commandArgs[3], &didError);
        data.destination = (RawDataErrorDestination)Utility::StringToU8(commandArgs[4], &didError);

        u8 requestHandle = commandArgsSize >= 6 ? Utility::StringToU8(commandArgs[5], &didError) : 0;

        if (didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

        GS->cm.SendModuleActionMessage(
            MessageType::MODULE_RAW_DATA,
            moduleId,
            receiverId,
            (u8)RawDataActionType::ERROR_T,
            requestHandle,
            (u8*)&data,
            sizeof(data),
            false,
            true
            );

        return TerminalCommandHandlerReturnType::SUCCESS;

    }
    //raw_data_start_received [receiverId] [destinationModule] {requestHandle = 0} {metadataHex = ""}
    else if (commandArgsSize >= 3 && TERMARGS(0, "raw_data_start_received"))
    {
        bool didError = false;
        
        NodeId receiverId = Utility::TerminalArgumentToNodeId(commandArgs[1], &didError);
        ModuleIdWrapper moduleId = Utility::GetWrappedModuleIdFromTerminal(commandArgs[2], &didError);

        u8 requestHandle = commandArgsSize >= 4 ? Utility::StringToU8(commandArgs[3], &didError) : 0;
        
        u8 metadata[MAX_RAW_DATA_METADATA_SIZE];
        CheckedMemset(metadata, 0x00, sizeof(metadata));
        u16 metadataLen = 0;
        if (commandArgsSize >= 5) {
            metadataLen = Logger::ParseEncodedStringToBuffer(commandArgs[4], metadata, MAX_RAW_DATA_METADATA_SIZE, &didError);
        }

        if (didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

        GS->cm.SendModuleActionMessage(
            MessageType::MODULE_RAW_DATA,
            moduleId,
            receiverId,
            (u8)RawDataActionType::START_RECEIVED,
            requestHandle,
            metadata,
            metadataLen,
            false,
            true
            );

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //raw_data_chunk [receiverId] [destinationModule] [chunkId] [payload] {requestHandle = 0}
    else if (commandArgsSize >= 5 && TERMARGS(0, "raw_data_chunk"))
    {
        bool didError = false;

        u8 buffer[MAX_MESH_PACKET_SIZE - sizeof(RawDataHeaderVendor)];
        CheckedMemset(&buffer, 0, sizeof(buffer));
        RawDataChunkPayload* data = (RawDataChunkPayload*)buffer;

        NodeId receiverId = Utility::TerminalArgumentToNodeId(commandArgs[1], &didError);
        ModuleIdWrapper moduleId = Utility::GetWrappedModuleIdFromTerminal(commandArgs[2], &didError);
        data->chunkId = Utility::StringToU32(commandArgs[3], &didError);
        u32 payloadLength = Logger::ParseEncodedStringToBuffer(commandArgs[4], data->payload, sizeof(buffer) - SIZEOF_RAW_DATA_CHUNK_PAYLOAD);
        u8 requestHandle = commandArgsSize >= 6 ? Utility::StringToU8(commandArgs[5], &didError) : 0;

        if (payloadLength == 0 || didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

        GS->cm.SendModuleActionMessage(
            MessageType::MODULE_RAW_DATA,
            moduleId,
            receiverId,
            (u8)RawDataActionType::CHUNK,
            requestHandle,
            buffer,
            SIZEOF_RAW_DATA_CHUNK_PAYLOAD + payloadLength,
            false,
            true
            );

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //raw_data_report [receiverId] [destinationModuleId] [missingChunkIds] {requestHandle = 0}
    else if (commandArgsSize >= 4 && TERMARGS(0, "raw_data_report"))
    {
        bool didError = false;
        RawDataReportPayload data;
        CheckedMemset(&data, 0x00, sizeof(data));

        NodeId receiverId = Utility::TerminalArgumentToNodeId(commandArgs[1], &didError);
        ModuleIdWrapper moduleId = Utility::GetWrappedModuleIdFromTerminal(commandArgs[2], &didError);

        //Parse the string of missing chunk ids which is comma seperated, such as e.g. 1,2,3
        if (strcmp(commandArgs[3], "-") != 0)
        {
            const char* readPtr = commandArgs[3];
            data.missings[0] = strtoul(readPtr, nullptr, 0);
            int missingIndex = 1;
            while (*readPtr != '\0')
            {
                if (*readPtr == ',')
                {
                    if (missingIndex == sizeof(data.missings) / sizeof(data.missings[0])) //Too many missings
                    {
                        return TerminalCommandHandlerReturnType::WRONG_ARGUMENT; //LCOV_EXCL_LINE assertion
                    }
                    data.missings[missingIndex] = strtoul(readPtr + 1, nullptr, 0);
                    missingIndex++;
                }
                readPtr++;
            }
        }

        u8 requestHandle = commandArgsSize >= 5 ? Utility::StringToU8(commandArgs[4], &didError) : 0;

        if (didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

        GS->cm.SendModuleActionMessage(
            MessageType::MODULE_RAW_DATA,
            moduleId,
            receiverId,
            (u8)RawDataActionType::REPORT,
            requestHandle,
            (u8*)&data,
            sizeof(data),
            false,
            true
            );

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //raw_data_report_desired [receiverId] [destinationModuleId] {requestHandle = 0}
    else if (commandArgsSize >= 3 && TERMARGS(0, "raw_data_report_desired"))
    {
        bool didError = false;

        NodeId receiverId = Utility::TerminalArgumentToNodeId(commandArgs[1], &didError);
        ModuleIdWrapper moduleId = Utility::GetWrappedModuleIdFromTerminal(commandArgs[2], &didError);

        u8 requestHandle = commandArgsSize >= 4 ? Utility::StringToU8(commandArgs[3], &didError) : 0;

        if (didError) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

        GS->cm.SendModuleActionMessage(
            MessageType::MODULE_RAW_DATA,
            moduleId,
            receiverId,
            (u8)RawDataActionType::REPORT_DESIRED,
            requestHandle,
            nullptr,
            0,
            false,
            true
            );

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    else if (commandArgsSize >= 2 && TERMARGS(0, "request_capability"))
    {
        CapabilityRequestedMessage message;
        CheckedMemset(&message, 0, sizeof(message));
        message.header.header.messageType = MessageType::CAPABILITY;
        message.header.header.sender      = configuration.nodeId;
        message.header.header.receiver    = Utility::TerminalArgumentToNodeId(commandArgs[1]);
        message.header.actionType         = CapabilityActionType::REQUESTED;

        //We don't allow broadcasts of the capability request
        //as it would put the mesh under heavy load.
        if (message.header.header.receiver == NODE_ID_BROADCAST)
        {
            return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;
        }

        GS->cm.SendMeshMessage(
            (u8*)&message,
            sizeof(CapabilityRequestedMessage));
        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //Set a timestamp for this node
    else if (TERMARGS(0, "settime") && commandArgsSize >= 3)
    {
        //Set the time for our node
        GS->timeManager.SetMasterTime(strtoul(commandArgs[1], nullptr, 10), 0, (i16)strtol(commandArgs[2], nullptr, 10));

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //Display the time of this node
    else if (TERMARGS(0, "gettime"))
    {
        char timestring[100];
        GS->timeManager.ConvertTimeToString(timestring, sizeof(timestring));

        if (GS->timeManager.IsTimeSynced())
        {
            trace("Time is currently %s" EOL, timestring);
        }
        else
        {
            trace("Time is currently not set: %s" EOL, timestring);
        }
        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    else if (TERMARGS(0, "startterm"))
    {
        Conf::GetInstance().terminalMode = TerminalMode::PROMPT;
        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    else if (TERMARGS(0, "stopterm"))
    {
        Conf::GetInstance().terminalMode = TerminalMode::JSON;
        return TerminalCommandHandlerReturnType::SUCCESS;
    }

    else if (TERMARGS(0, "set_serial") && commandArgsSize == 2)
    {
        if (!GS->config.enableMeshBridgeMode)
        {
            return TerminalCommandHandlerReturnType::UNKNOWN;
        }

        const auto serialNumberLength = strlen(commandArgs[1]);
        if (serialNumberLength != 5 && serialNumberLength != 7)
        {
            return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;
        }

        bool      getIndexForSerialError = false;
        const u32 serial                 = Utility::GetIndexForSerial(commandArgs[1], &getIndexForSerialError);
        if (getIndexForSerialError)
        {
            return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;
        }

        GS->config.SetSerialNumberIndex(serial);

        logt("NODE", "Serial Number Index set to %u", serial);

        return TerminalCommandHandlerReturnType::SUCCESS;
    }

    else if (TERMARGS(0, "set_node_key") && commandArgsSize == 2)
    {
        if (!GS->config.enableMeshBridgeMode) {
            return TerminalCommandHandlerReturnType::UNKNOWN;
        }

        u8 key[16];
        const u32 length = Logger::ParseEncodedStringToBuffer(commandArgs[1], key, sizeof(key));
        
        if (length != 16) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;

        GS->config.SetNodeKey(key);

        logt("NODE", "Node Key set to %s", commandArgs[1]);

        return TerminalCommandHandlerReturnType::SUCCESS;
    }


    /************* Debug commands ***************/
    else if (TERMARGS(0,"component_sense") && commandArgsSize >= 7)
    {
        SendComponentMessageFromTerminal(MessageType::COMPONENT_SENSE, commandArgs, commandArgsSize);

        return TerminalCommandHandlerReturnType::SUCCESS;
    }

    else if (TERMARGS(0,"component_act") && commandArgsSize >= 7)
    {
        SendComponentMessageFromTerminal(MessageType::COMPONENT_ACT, commandArgs, commandArgsSize);

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //Print the JOIN_ME buffer
    else if (TERMARGS(0, "bufferstat"))
    {
        PrintBufferStatus();
        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //Send some large data that is split over a few messages
    else if(TERMARGS(0, "datal"))
    {
        bool reliable = (commandArgsSize > 1 && TERMARGS(1 ,"r"));

        const u8 dataLength = 145;
        u8 _packet[dataLength];
        ConnPacketHeader* packet = (ConnPacketHeader*)_packet;
        packet->messageType = MessageType::DATA_1;
        packet->receiver = 0;
        packet->sender = configuration.nodeId;

        for(u32 i=0; i< dataLength-5; i++){
            _packet[i+5] = i+1;
        }
        
        ErrorType err = GS->cm.SendMeshMessageInternal(_packet, dataLength, reliable, true, true);
        if (err == ErrorType::SUCCESS) return TerminalCommandHandlerReturnType::SUCCESS;
        else return TerminalCommandHandlerReturnType::INTERNAL_ERROR;
    }
    //Stop the state machine
    else if (TERMARGS(0, "stop"))
    {
        DisableStateMachine(true);
        logt("NODE", "Stopping state machine.");
        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //Start the state machine
    else if (TERMARGS(0, "start"))
    {
        DisableStateMachine(false);
        logt("NODE", "Starting state machine.");

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //Disconnect a connection by its handle or all
    else if (TERMARGS(0, "disconnect"))
    {
        if(commandArgsSize <= 1) return TerminalCommandHandlerReturnType::NOT_ENOUGH_ARGUMENTS;
        if(TERMARGS(1 , "all")){
            GS->cm.ForceDisconnectAllConnections(AppDisconnectReason::USER_REQUEST);
        } else {
            BaseConnectionHandle conn = GS->cm.GetConnectionFromHandle(Utility::StringToU16(commandArgs[1]));
            if(conn){
                conn.DisconnectAndRemove(AppDisconnectReason::USER_REQUEST);
            }
        }

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //tell the gap layer to loose a connection
    else if (TERMARGS(0, "gap_disconnect"))
    {
        if(commandArgsSize <= 1) return TerminalCommandHandlerReturnType::NOT_ENOUGH_ARGUMENTS;
        u16 connectionHandle = Utility::StringToU16(commandArgs[1]);
        const ErrorType err = FruityHal::Disconnect(connectionHandle, FruityHal::BleHciError::REMOTE_USER_TERMINATED_CONNECTION);

        if (err != ErrorType::SUCCESS)
        {
            if (err == ErrorType::BLE_INVALID_CONN_HANDLE) return TerminalCommandHandlerReturnType::WRONG_ARGUMENT;
            return TerminalCommandHandlerReturnType::INTERNAL_ERROR;
        }

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    else if(TERMARGS(0, "update_iv"))     //jstodo can this be removed? Currently untested
    {
        if(commandArgsSize <= 2) return TerminalCommandHandlerReturnType::NOT_ENOUGH_ARGUMENTS;

        NodeId nodeId = Utility::StringToU16(commandArgs[1]);
        u16 newConnectionInterval = Utility::StringToU16(commandArgs[2]);

        #ifdef SIM_ENABLED
        // Neccessary for monkey-testing this command in combination with
        // the IllegalStateException that is thrown when the connection
        // interval does not match one of the values in the if-statements
        // at the end of CherrySim::SimulateBatteryUsage() (CherrySim.cpp).
        // This is not the best solution, but fixes the test and is not as
        // invasive as to silently change the connection interval while
        // setting it.
        switch (newConnectionInterval)
        {
            case MSEC_TO_UNITS(7, CONFIG_UNIT_1_25_MS):
            case MSEC_TO_UNITS(10, CONFIG_UNIT_1_25_MS):
            case MSEC_TO_UNITS(15, CONFIG_UNIT_1_25_MS):
            case MSEC_TO_UNITS(30, CONFIG_UNIT_1_25_MS):
            case MSEC_TO_UNITS(90, CONFIG_UNIT_1_25_MS):
            case MSEC_TO_UNITS(100, CONFIG_UNIT_1_25_MS):
                break;
            default:
                logt("WARNING", "Ignoring command because the connection interval is not valid for simulated battery measurements.");
                return TerminalCommandHandlerReturnType::INTERNAL_ERROR;
        }
        #endif

        ConnPacketUpdateConnectionInterval packet;
        packet.header.messageType = MessageType::UPDATE_CONNECTION_INTERVAL;
        packet.header.sender = GS->node.configuration.nodeId;
        packet.header.receiver = nodeId;

        packet.newInterval = newConnectionInterval;
        ErrorType err = GS->cm.SendMeshMessageInternal((u8*)&packet, SIZEOF_CONN_PACKET_UPDATE_CONNECTION_INTERVAL, true, true, true);
        if (err == ErrorType::SUCCESS) return TerminalCommandHandlerReturnType::SUCCESS;
        else return TerminalCommandHandlerReturnType::INTERNAL_ERROR;
    }
    /************* UART COMMANDS ***************/
    //Get the status information of this node
    else if(TERMARGS(0, "get_plugged_in"))
    {
        logjson("NODE", "{\"type\":\"plugged_in\",\"nodeId\":%u,\"serialNumber\":\"%s\",\"fmVersion\":%u}" SEP, configuration.nodeId, RamConfig->GetSerialNumber(), GS->config.GetFruityMeshVersion());
        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    //Query all modules from any node
    else if((TERMARGS(0, "get_modules")))
    {
        if(commandArgsSize <= 1) return TerminalCommandHandlerReturnType::NOT_ENOUGH_ARGUMENTS;

        NodeId receiver = Utility::TerminalArgumentToNodeId(commandArgs[1]);

        ConnPacketModule packet;
        packet.header.messageType = MessageType::MODULE_CONFIG;
        packet.header.sender = configuration.nodeId;
        packet.header.receiver = receiver;

        packet.moduleId = ModuleId::NODE;
        packet.requestHandle = 0;
        packet.actionType = (u8)Module::ModuleConfigMessages::GET_MODULE_LIST;

        GS->cm.SendMeshMessage((u8*) &packet, SIZEOF_CONN_PACKET_MODULE);

        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    else if(TERMARGS(0, "sep")){
        trace(EOL);
        for(u32 i=0; i<80*5; i++){
            if(i%80 == 0) trace(EOL);
            trace("#");
        }
        trace(EOL);
        trace(EOL);
        return TerminalCommandHandlerReturnType::SUCCESS;
    }
    else if (TERMARGS(0, "enable_corruption_check"))
    {
        logjson("NODE", "{\"type\":\"enable_corruption_check_response\",\"err\":0,\"check\":\"crc32\"}" SEP);
        GS->terminal.EnableCrcChecks();
        return TerminalCommandHandlerReturnType::SUCCESS;
    }
#if IS_ACTIVE(SIG_MESH)
    //Forwards TerminalCommandHandler to SigAccessLayer
    TerminalCommandHandlerReturnType ret = GS->sig.TerminalCommandHandler(commandArgs, commandArgsSize);
    if(ret != TerminalCommandHandlerReturnType::UNKNOWN) return ret;
#endif

    //Must be called to allow the module to get and set the config
    return Module::TerminalCommandHandler(commandArgs, commandArgsSize);
}

ErrorTypeUnchecked Node::SendComponentMessageFromTerminal(MessageType componentMessageType, const char* commandArgs[], u8 commandArgsSize)
{        
    ModuleIdWrapper moduleId = (ModuleIdWrapper)Utility::StringToU32(commandArgs[2]);

    u8 buffer[200];
    u16 payloadLength = 0;
    u16 totalLength;

    //We use a different packet format with an additional 3 bytes in case of a vendor module id
    if(Utility::IsVendorModuleId(moduleId))
    {
        ConnPacketComponentMessageVendor* message = (ConnPacketComponentMessageVendor*)buffer;
        message->componentHeader.header.messageType = componentMessageType;
        message->componentHeader.header.sender = configuration.nodeId;
        message->componentHeader.header.receiver = Utility::TerminalArgumentToNodeId(commandArgs[1]);
        message->componentHeader.moduleId = (VendorModuleId)moduleId;
        message->componentHeader.actionType = (u8)strtoul(commandArgs[3], nullptr, 0);
        message->componentHeader.component = (u16)strtoul(commandArgs[4], nullptr, 0);
        message->componentHeader.registerAddress = (u16)strtoul(commandArgs[5], nullptr, 0);
        message->componentHeader.requestHandle = (u8)((commandArgsSize > 7) ? strtoul(commandArgs[7], nullptr, 0) : 0);
        payloadLength = Logger::ParseEncodedStringToBuffer(commandArgs[6], message->payload, sizeof(buffer) - SIZEOF_COMPONENT_MESSAGE_HEADER_VENDOR);
        totalLength = SIZEOF_CONN_PACKET_COMPONENT_MESSAGE_VENDOR + payloadLength;
    }
    else
    {
        ConnPacketComponentMessage* message = (ConnPacketComponentMessage*)buffer;
        message->componentHeader.header.messageType = componentMessageType;
        message->componentHeader.header.sender = configuration.nodeId;
        message->componentHeader.header.receiver = Utility::TerminalArgumentToNodeId(commandArgs[1]);
        message->componentHeader.moduleId = Utility::GetModuleId(moduleId);
        message->componentHeader.actionType = (u8)strtoul(commandArgs[3], nullptr, 0);
        message->componentHeader.component = (u16)strtoul(commandArgs[4], nullptr, 0);
        message->componentHeader.registerAddress = (u16)strtoul(commandArgs[5], nullptr, 0);
        message->componentHeader.requestHandle = (u8)((commandArgsSize > 7) ? strtoul(commandArgs[7], nullptr, 0) : 0);
        payloadLength = Logger::ParseEncodedStringToBuffer(commandArgs[6], message->payload, sizeof(buffer) - SIZEOF_COMPONENT_MESSAGE_HEADER);
        totalLength = SIZEOF_CONN_PACKET_COMPONENT_MESSAGE + payloadLength;
    }

    GS->cm.SendMeshMessage(
        buffer,
        totalLength);

    return ErrorTypeUnchecked::SUCCESS;
}

#endif

inline void Node::SendModuleList(NodeId toNode, u8 requestHandle) const
{
    u16 bufferLength = GS->amountOfModules * sizeof(ModuleInformation);
    DYNAMIC_ARRAY(buffer, bufferLength);
    CheckedMemset(buffer, 0, bufferLength);

    //Iterate through all active modules to extract the necessary information
    for(u32 i = 0; i < GS->amountOfModules; i++)
    {
        ModuleInformation* info = (ModuleInformation*)(buffer + i * sizeof(ModuleInformation));

        if(!Utility::IsVendorModuleId(GS->activeModules[i]->moduleId)){
            info->moduleId = Utility::GetWrappedModuleId(GS->activeModules[i]->moduleId);
            info->moduleVersion = GS->activeModules[i]->configurationPointer->moduleVersion;
            info->moduleActive = GS->activeModules[i]->configurationPointer->moduleActive;
        } else {
            info->moduleId = GS->activeModules[i]->vendorModuleId;
            info->moduleVersion = GS->activeModules[i]->vendorConfigurationPointer->moduleVersion;
            info->moduleActive = GS->activeModules[i]->vendorConfigurationPointer->moduleActive;
        }
    }

    SendModuleActionMessage(
        MessageType::MODULE_CONFIG,
        toNode,
        (u8)Module::ModuleConfigMessages::MODULE_LIST_V2,
        requestHandle,
        buffer,
        bufferLength,
        false
    );
}


bool Node::IsPreferredConnection(NodeId id) const
{
    //If we don't have preferred connections set, any connection is treated as a preferred connection (every connection is equal).
    if (GS->config.configuration.amountOfPreferredPartnerIds == 0) return true;


    for (size_t i = 0; i < GS->config.configuration.amountOfPreferredPartnerIds; i++)
    {
        if (GS->config.configuration.preferredPartnerIds[i] == id)
        {
            return true;
        }
    }
    return false;
}

bool Node::CreateRawHeader(RawDataHeader* outVal, RawDataActionType type, const char* commandArgs[], const char* requestHandle) const
{
    if (requestHandle != nullptr)
    {
        outVal->requestHandle = Utility::StringToU8(requestHandle);
    }

    outVal->connHeader.messageType = MessageType::MODULE_RAW_DATA;
    outVal->connHeader.sender = configuration.nodeId;
    outVal->connHeader.receiver = Utility::TerminalArgumentToNodeId(commandArgs[1]);

    ModuleIdWrapper moduleId = Utility::GetWrappedModuleIdFromTerminal(commandArgs[2]);
    
    if(Utility::IsVendorModuleId(moduleId)){
        logt("ERROR", "raw data currently not implemented for vendor modules");
        return false;
    }

    outVal->moduleId = Utility::GetModuleId(moduleId);
    outVal->actionType = type;


    return true;
}

void Node::Reboot(u32 delayDs, RebootReason reason)
{
    u32 newRebootTimeDs = GS->appTimerDs + delayDs;
    // Only store the new reboot reason if it happens before the previously set reboot reason or if no reboot reason was set yet.
    // The reason for this is that if two different reboots are logically "queued", the later one has no effect, because the
    // earlier one has already taken effect, eliminating the later reboot. Thus at every time only a single reboot actually must
    // be rememberd which is the one that happens the earliest.
    if (rebootTimeDs == 0 || newRebootTimeDs < rebootTimeDs)
    {
        rebootTimeDs = newRebootTimeDs;
        GS->ramRetainStructPtr->rebootReason = reason;
    }
}

bool Node::IsRebootScheduled()
{
    return rebootTimeDs != 0;
}

/* EOF */
