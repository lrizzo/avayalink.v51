/*
 * AvayaLinkView.java
 *
 * Lawrence J. Rizzo, 10/11/2010
 *
 * This class uses Avaya SMS and JTAPI to monitor station phone events.  It
 * also hosts a socket server to process software commands to control the 
 * agents phone.  (dial, hangup, etc.)
 */
package avayalink;
//
import static avayalink.CUBS.CUBSDB.*;
import static avayalink.AvayaLinkApp.ApplicationLog;
import avayalink.CommandTypes.CommandType;
import avayalink.ErrorTypes.ErrorType;
//
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.InputEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.sql.Timestamp;
import java.util.Calendar;
import java.util.Collection;
import java.util.Enumeration;
import java.util.EventObject;
import java.util.TimerTask;
import java.util.concurrent.ConcurrentHashMap;
import javax.swing.Icon;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.SwingUtilities;
import javax.swing.Timer;
import javax.telephony.Address;
import javax.telephony.CallListener;
import javax.telephony.Connection;
import javax.telephony.JtapiPeer;
import javax.telephony.JtapiPeerFactory;
import javax.telephony.JtapiPeerUnavailableException;
import javax.telephony.Provider;
import javax.telephony.ProviderEvent;
import javax.telephony.ProviderListener;
import javax.telephony.Terminal;
import javax.telephony.TerminalConnection;
import javax.telephony.callcenter.Agent;
import javax.telephony.callcenter.AgentTerminal;
import javax.telephony.callcontrol.CallControlConnectionEvent;
import javax.telephony.callcontrol.CallControlEvent;
import javax.telephony.callcontrol.CallControlTerminalConnection;
import mytextarea.MyTextArea;
import org.jdesktop.application.Action;
import org.jdesktop.application.Application.ExitListener;
import org.jdesktop.application.FrameView;
import org.jdesktop.application.ResourceMap;
import org.jdesktop.application.SingleFrameApplication;
import org.jdesktop.application.Task;
import org.jdesktop.application.TaskMonitor;
import avayalink.config.SiteConfigurationSettings;
import avayalink.searchDND.ValidatePhoneNumber;
import avayalink.server.SocketServer;
import avayalink.server.events.DialEvent;
import avayalink.server.events.GetAgentExtensionEvent;
import avayalink.server.events.GetAgentIdEvent;
import avayalink.server.events.GetStationInfoEvent;
import avayalink.server.events.HangupEvent;
import avayalink.server.events.NewSocketLogMessageEvent;
import avayalink.server.events.SocketCommandListener;
import avayalink.server.events.SocketLogMessageListener;
import avayalink.server.events.UnknownSocketCommandEvent;
import com.avaya.jtapi.tsapi.ITsapiProvider;
import com.avaya.jtapi.tsapi.ITsapiProviderEx;
import com.avaya.jtapi.tsapi.LucentCallEx2;
import com.avaya.jtapi.tsapi.LucentV5CallInfo;
import com.avaya.jtapi.tsapi.TsapiInvalidArgumentException;
import com.avaya.jtapi.tsapi.TsapiInvalidPartyException;
import com.avaya.jtapi.tsapi.TsapiInvalidStateException;
import com.avaya.jtapi.tsapi.TsapiPlatformException;
import com.avaya.jtapi.tsapi.TsapiResourceUnavailableException;
import com.avaya.jtapi.tsapi.UserToUserInfo;
import com.avaya.jtapi.tsapi.adapters.CallControlConnectionListenerAdapter;
import Avayacom.avaya.smsxml.ModelChoices;
import Avayacom.avaya.smsxml.ObjectFactory;
import Avayacom.avaya.smsxml.StationType;
import avayalink.server.events.WarmTransferEvent;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.Map.Entry;
import static javax.telephony.Event.CAUSE_NORMAL;
import javax.telephony.InvalidArgumentException;
import javax.telephony.InvalidStateException;
import javax.telephony.MethodNotSupportedException;
import javax.telephony.PrivilegeViolationException;
import javax.telephony.ResourceUnavailableException;

public class AvayaLinkView extends FrameView implements ProviderListener, SocketLogMessageListener {
    public SiteConfigurationSettings configurationSetting;
    private final boolean LOGCALLS = true;
    private final boolean TRANSFERDNDCALLS = false;
    private final boolean TRANSFERMANUALCALLS = false;
    private final int EXTENSIONLENGTH = 5;
//        
    private boolean AESServerOnline = false;
    private final int HEARTBEAT_INTERVAL = 10;
    private final String SOCKET_FIELD_DELIMITER = "|";
    private final String UNIT_SEPERATOR = "\\";
    private SortList sortedExtensionList = new SortList();
    private ConcurrentHashMap<String, String> avayaAgentIDs = new ConcurrentHashMap<>();
    private ConcurrentHashMap<String, AvayaStationData> smsStationExtensions = new ConcurrentHashMap<>();
    private ConcurrentHashMap<String, AvayaAgent> extensionsBeingMonitored = new ConcurrentHashMap<>();
    private int extensionsBeingMonitoredCount = 0;
    private ConcurrentHashMap<String, String> extensionsNotBeingMonitored = new ConcurrentHashMap<>();
    private int extensionsNotBeingMonitoredCount = 0;
    private ConcurrentHashMap<String, AvayaCall> currentAvayaCalls = new ConcurrentHashMap<>();
    private int extensionsMonitorErrorCount = 0;    
//    
    private java.util.Timer uvKeepAliveTimer;
    private java.util.Timer smsTimer;
    private JtapiPeer jtapiPeer = null;
    private Provider provider;
    private ITsapiProviderEx tsprovider;
    private String errorMessage = "";
    private ObjectFactory objectFactory;
    private final MyTextArea eventLogWindow;
    private final MyTextArea socketLogWindow;
    private static final boolean IS_DEV_MODE = false;

    public AvayaLinkView(SingleFrameApplication app, SiteConfigurationSettings settings) {
        super(app);
        initComponents();

        // Load configuration settings
        this.configurationSetting = settings;

        // status bar initialization - message timeout, idle icon and busy animation, etc
        ResourceMap resourceMap = getResourceMap();
        int messageTimeout = resourceMap.getInteger("StatusBar.messageTimeout");
        messageTimer = new Timer(messageTimeout, new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {
                statusMessageLabel.setText("");
            }
        });
        messageTimer.setRepeats(false);
        int busyAnimationRate = resourceMap.getInteger("StatusBar.busyAnimationRate");
        for (int i = 0; i < busyIcons.length; i++) {
            busyIcons[i] = resourceMap.getIcon("StatusBar.busyIcons[" + i + "]");
        }
        busyIconTimer = new Timer(busyAnimationRate, new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {
                busyIconIndex = (busyIconIndex + 1) % busyIcons.length;
                statusAnimationLabel.setIcon(busyIcons[busyIconIndex]);
            }
        });
        idleIcon = resourceMap.getIcon("StatusBar.idleIcon");
        statusAnimationLabel.setIcon(idleIcon);
        progressBar.setVisible(false);
        chkAllowManualDialing.setVisible(false);
        chkShowDNDs.setVisible(false);
        
        // connecting action tasks to status bar via TaskMonitor
        TaskMonitor taskMonitor = new TaskMonitor(getApplication().getContext());
        taskMonitor.addPropertyChangeListener(new java.beans.PropertyChangeListener() {

            @Override
            public void propertyChange(java.beans.PropertyChangeEvent evt) {
                String propertyName = evt.getPropertyName();
                if ("started".equals(propertyName)) {
                    if (!busyIconTimer.isRunning()) {
                        statusAnimationLabel.setIcon(busyIcons[0]);
                        busyIconIndex = 0;
                        busyIconTimer.start();
                    }
                    progressBar.setVisible(true);
                    progressBar.setIndeterminate(true);
                } else if ("done".equals(propertyName)) {
                    busyIconTimer.stop();
                    statusAnimationLabel.setIcon(idleIcon);
                    progressBar.setVisible(false);
                    progressBar.setValue(0);
                } else if ("message".equals(propertyName)) {
                    String text = (String) (evt.getNewValue());
                    statusMessageLabel.setText((text == null) ? "" : text);
                    messageTimer.restart();
                } else if ("progress".equals(propertyName)) {
                    int value = (Integer) (evt.getNewValue());
                    progressBar.setVisible(true);
                    progressBar.setIndeterminate(false);
                    progressBar.setValue(value);
                }
            }
        });

        // Set font for extension list
        lstExtensionsBeingMonitored.setFont(Font.getFont("Consolas-Plain-12"));

        // Setup mouse listener for extension list events
        lstExtensionsBeingMonitored.addMouseListener(mouseListener);

        // Setup window listener
        AvayaLinkApp.getApplication().addExitListener(new ExitListener() {

            @Override
            public boolean canExit(EventObject arg0) {
                return QuitApplication();
            }

            @Override
            public void willExit(EventObject arg0) {
        
            }
        });

        // Initialize log windows (move?)
        eventLogWindow = this.txtSessionLog;
        eventLogWindow.LogType = "EVENT";
        eventLogWindow.SelectedExtensions = null;
        SetEventLogFilters();

        socketLogWindow = this.txtCommandLog;
        socketLogWindow.LogType = "SOCKET";
        socketLogWindow.SelectedExtensions = null;
        SetEventLogFilters();
    }

    public static boolean writeInboundCall(String filename, String textToWrite) {
        boolean retVal = false;

        SiteConfigurationSettings settings = AvayaLinkApp.getApplication().getSelectedSettings();

        try {
            String fileWithPath = settings.getPrimaryCallOutputFilePath() + filename;
            retVal = writeTextToFile(fileWithPath, textToWrite);
        } catch (Exception e) {
            //if we fail, we should write to secondary log and report error to admin
            try {
                String fileWithPath = settings.getSecondaryCallOutputFilePath() + filename;
                retVal = writeTextToFile(fileWithPath, textToWrite);
                ErrorReportManager.reportErrorByEmail("AvayaLink call output error", "A record was written to the secondary file output path.  " + e.getMessage());
            } catch (Exception ex) {
                ex.printStackTrace();
            }
        }

        return retVal;        
    }    
    
    public static boolean writeCallOutcome(String filename, String textToWrite) {
        boolean retVal = false;

        SiteConfigurationSettings settings = AvayaLinkApp.getApplication().getSelectedSettings();

        try {
            String fileWithPath = settings.getPrimaryCallOutputFilePath() + filename;
            retVal = writeTextToFile(fileWithPath, textToWrite);
        } catch (Exception e) {
            //if we fail, we should write to secondary log and report error to admin
            try {
                String fileWithPath = settings.getSecondaryCallOutputFilePath() + filename;
                retVal = writeTextToFile(fileWithPath, textToWrite);
                ErrorReportManager.reportErrorByEmail("AvayaLink call output error", "A record was written to the secondary file output path.  " + e.getMessage());
            } catch (Exception ex) {
                ex.printStackTrace();
            }
        }

        return retVal;
    }

    public static boolean writeTextToFile(String filenameWithPath, String textToWrite) throws Exception {
        boolean success = false;
        
        try (PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(filenameWithPath)))) {
            out.write(textToWrite);
            out.flush();
            success = true;
        } catch (Exception e) {
            throw e;
        }

        return success;
    }

    @Action
    public void showAboutBox() {
        if (aboutBox == null) {
            JFrame mainFrame = AvayaLinkApp.getApplication().getMainFrame();
            aboutBox = new AvayaLinkAboutBox(mainFrame);
            aboutBox.setLocationRelativeTo(mainFrame);
        }
        
        AvayaLinkApp.getApplication().show(aboutBox);        
    }

    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        mainPanel = new javax.swing.JPanel();
        sppSplitter = new javax.swing.JSplitPane();
        txtSessionLog = new mytextarea.MyTextArea();
        txtCommandLog = new mytextarea.MyTextArea();
        jScrollPane1 = new javax.swing.JScrollPane();
        lstExtensionsBeingMonitored = new javax.swing.JList();
        lblHeartbeatText = new javax.swing.JLabel();
        jPanel1 = new javax.swing.JPanel();
        jPanel2 = new javax.swing.JPanel();
        chkShowDials = new javax.swing.JCheckBox();
        chkShowHangups = new javax.swing.JCheckBox();
        chkSocketFilterExtensions = new javax.swing.JCheckBox();
        chkAllowManualDialing = new javax.swing.JCheckBox();
        btnSocketResetDefault = new javax.swing.JButton();
        chkShowTransfers = new javax.swing.JCheckBox();
        jPanel3 = new javax.swing.JPanel();
        chkShowConnects = new javax.swing.JCheckBox();
        chkShowDisconnects = new javax.swing.JCheckBox();
        chkShowRegistrations = new javax.swing.JCheckBox();
        chkEventFilterExtensions = new javax.swing.JCheckBox();
        btnEventResetDefault = new javax.swing.JButton();
        chkShowDeregistrations = new javax.swing.JCheckBox();
        chkShowDNDs = new javax.swing.JCheckBox();
        chkShowWarnings = new javax.swing.JCheckBox();
        chkShowFailures = new javax.swing.JCheckBox();
        cmdStartMonitor = new javax.swing.JButton();
        cmdExitApplication = new javax.swing.JButton();
        menuBar = new javax.swing.JMenuBar();
        javax.swing.JMenu fileMenu = new javax.swing.JMenu();
        javax.swing.JMenuItem exitMenuItem = new javax.swing.JMenuItem();
        fileView = new javax.swing.JMenu();
        viewStationMenuItem = new javax.swing.JMenuItem();
        javax.swing.JMenu helpMenu = new javax.swing.JMenu();
        javax.swing.JMenuItem aboutMenuItem = new javax.swing.JMenuItem();
        statusPanel = new javax.swing.JPanel();
        javax.swing.JSeparator statusPanelSeparator = new javax.swing.JSeparator();
        statusMessageLabel = new javax.swing.JLabel();
        statusAnimationLabel = new javax.swing.JLabel();
        progressBar = new javax.swing.JProgressBar();
        lblExtensionsBeingMonitored = new javax.swing.JLabel();
        popExtensionsBeingMonitored = new javax.swing.JPopupMenu();
        popViewAvayaStation = new javax.swing.JMenuItem();

        mainPanel.setMinimumSize(new java.awt.Dimension(1055, 587));
        mainPanel.setName("mainPanel"); // NOI18N

        sppSplitter.setBorder(javax.swing.BorderFactory.createEtchedBorder());
        sppSplitter.setDividerLocation(330);
        sppSplitter.setOrientation(javax.swing.JSplitPane.VERTICAL_SPLIT);
        sppSplitter.setName("sppSplitter"); // NOI18N
        sppSplitter.setNextFocusableComponent(cmdStartMonitor);

        txtSessionLog.setCursor(new java.awt.Cursor(java.awt.Cursor.TEXT_CURSOR));
        org.jdesktop.application.ResourceMap resourceMap = org.jdesktop.application.Application.getInstance(avayalink.AvayaLinkApp.class).getContext().getResourceMap(AvayaLinkView.class);
        txtSessionLog.setFont(resourceMap.getFont("txtSessionLog.font")); // NOI18N
        txtSessionLog.setName("txtSessionLog"); // NOI18N
        sppSplitter.setLeftComponent(txtSessionLog);

        txtCommandLog.setFont(resourceMap.getFont("txtCommandLog.font")); // NOI18N
        txtCommandLog.setName("txtCommandLog"); // NOI18N
        sppSplitter.setRightComponent(txtCommandLog);

        jScrollPane1.setName("jScrollPane1"); // NOI18N

        lstExtensionsBeingMonitored.setBorder(javax.swing.BorderFactory.createEtchedBorder());
        lstExtensionsBeingMonitored.setFont(resourceMap.getFont("jListExtensionsMonitored.font")); // NOI18N
        lstExtensionsBeingMonitored.setName("jListExtensionsMonitored"); // NOI18N
        lstExtensionsBeingMonitored.addListSelectionListener(new javax.swing.event.ListSelectionListener() {
            public void valueChanged(javax.swing.event.ListSelectionEvent evt) {
                lstExtensionsBeingMonitoredValueChanged(evt);
            }
        });
        jScrollPane1.setViewportView(lstExtensionsBeingMonitored);

        lblHeartbeatText.setBorder(javax.swing.BorderFactory.createEtchedBorder());
        lblHeartbeatText.setName("lblHeartbeatText"); // NOI18N

        jPanel1.setBorder(javax.swing.BorderFactory.createTitledBorder("Filters"));
        jPanel1.setName("jPanel1"); // NOI18N

        jPanel2.setBorder(javax.swing.BorderFactory.createTitledBorder("Socket Log"));
        jPanel2.setName("jPanel2"); // NOI18N

        javax.swing.ActionMap actionMap = org.jdesktop.application.Application.getInstance(avayalink.AvayaLinkApp.class).getContext().getActionMap(AvayaLinkView.class, this);
        chkShowDials.setAction(actionMap.get("SetSocketLogFilters")); // NOI18N
        chkShowDials.setSelected(true);
        chkShowDials.setText(resourceMap.getString("chkShowDials.text")); // NOI18N
        chkShowDials.setName("chkShowDials"); // NOI18N

        chkShowHangups.setAction(actionMap.get("SetSocketLogFilters")); // NOI18N
        chkShowHangups.setSelected(true);
        chkShowHangups.setText(resourceMap.getString("chkShowHangups.text")); // NOI18N
        chkShowHangups.setName("chkShowHangups"); // NOI18N

        chkSocketFilterExtensions.setAction(actionMap.get("SetSocketLogFilters")); // NOI18N
        chkSocketFilterExtensions.setText(resourceMap.getString("chkSocketFilterExtensions.text")); // NOI18N
        chkSocketFilterExtensions.setName("chkSocketFilterExtensions"); // NOI18N

        chkAllowManualDialing.setAction(actionMap.get("SetSocketLogFilters")); // NOI18N
        chkAllowManualDialing.setText(resourceMap.getString("chkAllowManualDialing.text")); // NOI18N
        chkAllowManualDialing.setName("chkAllowManualDialing"); // NOI18N

        btnSocketResetDefault.setAction(actionMap.get("SocketLogResetDefault")); // NOI18N
        btnSocketResetDefault.setText(resourceMap.getString("btnSocketResetDefault.text")); // NOI18N
        btnSocketResetDefault.setName("btnSocketResetDefault"); // NOI18N

        chkShowTransfers.setAction(actionMap.get("SetSocketLogFilters")); // NOI18N
        chkShowTransfers.setSelected(true);
        chkShowTransfers.setText(resourceMap.getString("chkShowTransfers.text")); // NOI18N
        chkShowTransfers.setName("chkShowTransfers"); // NOI18N

        javax.swing.GroupLayout jPanel2Layout = new javax.swing.GroupLayout(jPanel2);
        jPanel2.setLayout(jPanel2Layout);
        jPanel2Layout.setHorizontalGroup(
            jPanel2Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(jPanel2Layout.createSequentialGroup()
                .addGap(14, 14, 14)
                .addGroup(jPanel2Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(chkAllowManualDialing, javax.swing.GroupLayout.PREFERRED_SIZE, 193, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addGroup(jPanel2Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.TRAILING, false)
                        .addComponent(chkShowDials, javax.swing.GroupLayout.Alignment.LEADING, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                        .addComponent(chkShowHangups, javax.swing.GroupLayout.Alignment.LEADING, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                        .addComponent(chkShowTransfers, javax.swing.GroupLayout.Alignment.LEADING, javax.swing.GroupLayout.DEFAULT_SIZE, 178, Short.MAX_VALUE))
                    .addGroup(jPanel2Layout.createSequentialGroup()
                        .addGap(1, 1, 1)
                        .addGroup(jPanel2Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.TRAILING)
                            .addComponent(chkSocketFilterExtensions)
                            .addComponent(btnSocketResetDefault))))
                .addContainerGap(28, Short.MAX_VALUE))
        );
        jPanel2Layout.setVerticalGroup(
            jPanel2Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(javax.swing.GroupLayout.Alignment.TRAILING, jPanel2Layout.createSequentialGroup()
                .addComponent(chkShowDials)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(chkShowTransfers)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(chkShowHangups)
                .addGap(18, 18, 18)
                .addComponent(chkSocketFilterExtensions)
                .addGap(7, 7, 7)
                .addComponent(btnSocketResetDefault)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(chkAllowManualDialing)
                .addContainerGap())
        );

        jPanel3.setBorder(javax.swing.BorderFactory.createTitledBorder("Event Log"));
        jPanel3.setName("jPanel3"); // NOI18N

        chkShowConnects.setAction(actionMap.get("SetEventLogFilters")); // NOI18N
        chkShowConnects.setSelected(true);
        chkShowConnects.setText(resourceMap.getString("chkShowConnects.text")); // NOI18N

        chkShowDisconnects.setAction(actionMap.get("SetEventLogFilters")); // NOI18N
        chkShowDisconnects.setSelected(true);
        chkShowDisconnects.setText(resourceMap.getString("chkShowDisconnects.text")); // NOI18N

        chkShowRegistrations.setAction(actionMap.get("SetEventLogFilters")); // NOI18N
        chkShowRegistrations.setText(resourceMap.getString("chkShowRegistrations.text")); // NOI18N

        chkEventFilterExtensions.setAction(actionMap.get("SetEventLogFilters")); // NOI18N
        chkEventFilterExtensions.setText(resourceMap.getString("chkEventFilterExtensions.text")); // NOI18N
        chkEventFilterExtensions.setName("chkEventFilterExtensions"); // NOI18N

        btnEventResetDefault.setAction(actionMap.get("EventLogResetDefault")); // NOI18N
        btnEventResetDefault.setText(resourceMap.getString("btnEventResetDefault.text")); // NOI18N
        btnEventResetDefault.setName("btnEventResetDefault"); // NOI18N

        chkShowDeregistrations.setAction(actionMap.get("SetEventLogFilters")); // NOI18N
        chkShowDeregistrations.setSelected(true);
        chkShowDeregistrations.setText(resourceMap.getString("chkShowDeregistrations.text")); // NOI18N
        chkShowDeregistrations.setName("chkShowDeregistrations"); // NOI18N

        chkShowDNDs.setAction(actionMap.get("SetEventLogFilters")); // NOI18N
        chkShowDNDs.setSelected(true);
        chkShowDNDs.setText(resourceMap.getString("chkShowDNDs.text")); // NOI18N
        chkShowDNDs.setName("chkShowDNDs"); // NOI18N

        chkShowWarnings.setAction(actionMap.get("SetEventLogFilters")); // NOI18N
        chkShowWarnings.setSelected(true);
        chkShowWarnings.setText(resourceMap.getString("chkShowWarnings.text")); // NOI18N
        chkShowWarnings.setName("chkShowWarnings"); // NOI18N

        chkShowFailures.setAction(actionMap.get("SetEventLogFilters")); // NOI18N
        chkShowFailures.setSelected(true);
        chkShowFailures.setText(resourceMap.getString("chkShowFailures.text")); // NOI18N
        chkShowFailures.setName("chkShowFailures"); // NOI18N

        javax.swing.GroupLayout jPanel3Layout = new javax.swing.GroupLayout(jPanel3);
        jPanel3.setLayout(jPanel3Layout);
        jPanel3Layout.setHorizontalGroup(
            jPanel3Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(jPanel3Layout.createSequentialGroup()
                .addGap(15, 15, 15)
                .addGroup(jPanel3Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(chkShowFailures)
                    .addGroup(jPanel3Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING, false)
                        .addComponent(chkShowDisconnects, javax.swing.GroupLayout.DEFAULT_SIZE, 177, Short.MAX_VALUE)
                        .addComponent(chkShowWarnings)
                        .addComponent(chkShowDNDs))
                    .addGroup(jPanel3Layout.createSequentialGroup()
                        .addGap(22, 22, 22)
                        .addComponent(btnEventResetDefault))
                    .addComponent(chkEventFilterExtensions)
                    .addGroup(jPanel3Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING, false)
                        .addComponent(chkShowDeregistrations)
                        .addComponent(chkShowRegistrations, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                        .addComponent(chkShowConnects)))
                .addContainerGap(33, Short.MAX_VALUE))
        );
        jPanel3Layout.setVerticalGroup(
            jPanel3Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(jPanel3Layout.createSequentialGroup()
                .addContainerGap()
                .addComponent(chkShowRegistrations)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(chkShowDeregistrations)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(chkShowConnects)
                .addGap(1, 1, 1)
                .addComponent(chkShowFailures)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(chkShowDisconnects)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(chkShowWarnings)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(chkShowDNDs)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, 27, Short.MAX_VALUE)
                .addComponent(chkEventFilterExtensions)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                .addComponent(btnEventResetDefault)
                .addGap(16, 16, 16))
        );

        javax.swing.GroupLayout jPanel1Layout = new javax.swing.GroupLayout(jPanel1);
        jPanel1.setLayout(jPanel1Layout);
        jPanel1Layout.setHorizontalGroup(
            jPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(jPanel1Layout.createSequentialGroup()
                .addContainerGap()
                .addGroup(jPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.TRAILING, false)
                    .addComponent(jPanel2, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                    .addComponent(jPanel3, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
                .addContainerGap())
        );
        jPanel1Layout.setVerticalGroup(
            jPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(javax.swing.GroupLayout.Alignment.TRAILING, jPanel1Layout.createSequentialGroup()
                .addComponent(jPanel3, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                .addComponent(jPanel2, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                .addContainerGap())
        );

        cmdStartMonitor.setAction(actionMap.get("StartMonitor")); // NOI18N
        cmdStartMonitor.setText(resourceMap.getString("cmdStartMonitor.text")); // NOI18N
        cmdStartMonitor.setName("cmdStartMonitor"); // NOI18N

        cmdExitApplication.setText(resourceMap.getString("cmdExit.text")); // NOI18N
        cmdExitApplication.setName("cmdExit"); // NOI18N
        cmdExitApplication.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                cmdExitApplicationActionPerformed(evt);
            }
        });

        javax.swing.GroupLayout mainPanelLayout = new javax.swing.GroupLayout(mainPanel);
        mainPanel.setLayout(mainPanelLayout);
        mainPanelLayout.setHorizontalGroup(
            mainPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(mainPanelLayout.createSequentialGroup()
                .addContainerGap()
                .addGroup(mainPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addGroup(mainPanelLayout.createSequentialGroup()
                        .addComponent(jScrollPane1, javax.swing.GroupLayout.PREFERRED_SIZE, 82, javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                        .addComponent(sppSplitter, javax.swing.GroupLayout.DEFAULT_SIZE, 735, Short.MAX_VALUE))
                    .addComponent(lblHeartbeatText, javax.swing.GroupLayout.Alignment.TRAILING, javax.swing.GroupLayout.DEFAULT_SIZE, 823, Short.MAX_VALUE))
                .addGroup(mainPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addGroup(mainPanelLayout.createSequentialGroup()
                        .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                        .addComponent(jPanel1, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE))
                    .addGroup(mainPanelLayout.createSequentialGroup()
                        .addGap(33, 33, 33)
                        .addComponent(cmdStartMonitor, javax.swing.GroupLayout.PREFERRED_SIZE, 108, javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                        .addComponent(cmdExitApplication, javax.swing.GroupLayout.PREFERRED_SIZE, 103, javax.swing.GroupLayout.PREFERRED_SIZE)))
                .addContainerGap())
        );
        mainPanelLayout.setVerticalGroup(
            mainPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(mainPanelLayout.createSequentialGroup()
                .addGap(13, 13, 13)
                .addGroup(mainPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.TRAILING)
                    .addComponent(jPanel1, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                    .addComponent(jScrollPane1, javax.swing.GroupLayout.Alignment.LEADING, javax.swing.GroupLayout.DEFAULT_SIZE, 528, Short.MAX_VALUE)
                    .addComponent(sppSplitter, javax.swing.GroupLayout.Alignment.LEADING, javax.swing.GroupLayout.DEFAULT_SIZE, 528, Short.MAX_VALUE))
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addGroup(mainPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.TRAILING)
                    .addComponent(lblHeartbeatText, javax.swing.GroupLayout.PREFERRED_SIZE, 23, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addGroup(mainPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                        .addComponent(cmdStartMonitor)
                        .addComponent(cmdExitApplication)))
                .addGap(11, 11, 11))
        );

        menuBar.setName("menuBar"); // NOI18N

        fileMenu.setText(resourceMap.getString("fileMenu.text")); // NOI18N
        fileMenu.setName("fileMenu"); // NOI18N

        exitMenuItem.setAction(actionMap.get("quit")); // NOI18N
        exitMenuItem.setName("exitMenuItem"); // NOI18N
        fileMenu.add(exitMenuItem);

        menuBar.add(fileMenu);

        fileView.setText(resourceMap.getString("fileView.text")); // NOI18N
        fileView.setName("fileView"); // NOI18N

        viewStationMenuItem.setAction(actionMap.get("ViewStationData")); // NOI18N
        viewStationMenuItem.setText(resourceMap.getString("viewStationMenuItem.text")); // NOI18N
        viewStationMenuItem.setName("viewStationMenuItem"); // NOI18N
        fileView.add(viewStationMenuItem);

        menuBar.add(fileView);

        helpMenu.setText(resourceMap.getString("helpMenu.text")); // NOI18N
        helpMenu.setName("helpMenu"); // NOI18N

        aboutMenuItem.setAction(actionMap.get("showAboutBox")); // NOI18N
        aboutMenuItem.setName("aboutMenuItem"); // NOI18N
        helpMenu.add(aboutMenuItem);

        menuBar.add(helpMenu);

        statusPanel.setName("statusPanel"); // NOI18N

        statusPanelSeparator.setName("statusPanelSeparator"); // NOI18N

        statusMessageLabel.setName("statusMessageLabel"); // NOI18N

        statusAnimationLabel.setHorizontalAlignment(javax.swing.SwingConstants.LEFT);
        statusAnimationLabel.setName("statusAnimationLabel"); // NOI18N

        progressBar.setName("progressBar"); // NOI18N

        lblExtensionsBeingMonitored.setName("lblExtensionsBeingMonitored"); // NOI18N

        javax.swing.GroupLayout statusPanelLayout = new javax.swing.GroupLayout(statusPanel);
        statusPanel.setLayout(statusPanelLayout);
        statusPanelLayout.setHorizontalGroup(
            statusPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addComponent(statusPanelSeparator, javax.swing.GroupLayout.DEFAULT_SIZE, 1128, Short.MAX_VALUE)
            .addGroup(statusPanelLayout.createSequentialGroup()
                .addContainerGap()
                .addComponent(statusMessageLabel)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(lblExtensionsBeingMonitored, javax.swing.GroupLayout.DEFAULT_SIZE, 942, Short.MAX_VALUE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                .addComponent(progressBar, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(statusAnimationLabel)
                .addContainerGap())
        );
        statusPanelLayout.setVerticalGroup(
            statusPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(statusPanelLayout.createSequentialGroup()
                .addGap(0, 0, Short.MAX_VALUE)
                .addComponent(statusPanelSeparator, javax.swing.GroupLayout.PREFERRED_SIZE, 2, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addGroup(statusPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.TRAILING)
                    .addGroup(statusPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                        .addComponent(statusMessageLabel)
                        .addComponent(statusAnimationLabel)
                        .addComponent(progressBar, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE))
                    .addComponent(lblExtensionsBeingMonitored, javax.swing.GroupLayout.PREFERRED_SIZE, 16, javax.swing.GroupLayout.PREFERRED_SIZE))
                .addGap(11, 11, 11))
        );

        popExtensionsBeingMonitored.setName("popExtensionsBeingMonitored"); // NOI18N

        popViewAvayaStation.setAction(actionMap.get("ViewStationData")); // NOI18N
        popViewAvayaStation.setText(resourceMap.getString("popViewAvayaStation.text")); // NOI18N
        popViewAvayaStation.setName("popViewAvayaStation"); // NOI18N
        popExtensionsBeingMonitored.add(popViewAvayaStation);

        setComponent(mainPanel);
        setMenuBar(menuBar);
        setStatusBar(statusPanel);
    }// </editor-fold>//GEN-END:initComponents

    private void cmdExitApplicationActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_cmdExitApplicationActionPerformed
        if (QuitApplication()) {
            System.exit(0);
        }
    }//GEN-LAST:event_cmdExitApplicationActionPerformed

    private void lstExtensionsBeingMonitoredValueChanged(javax.swing.event.ListSelectionEvent evt) {//GEN-FIRST:event_lstExtensionsBeingMonitoredValueChanged
        Object[] selectedExtensions;
        selectedExtensions = (Object[]) lstExtensionsBeingMonitored.getSelectedValues();

        eventLogWindow.SelectedExtensions = selectedExtensions;
        socketLogWindow.SelectedExtensions = selectedExtensions;
    }//GEN-LAST:event_lstExtensionsBeingMonitoredValueChanged

    private boolean initJtapi() {
        try {
            // get default implementation of the JtapiPeer object by sending null
            // optionally you may send com.avaya.jtapi.tsapi.TsapiPeer
            jtapiPeer = JtapiPeerFactory.getJtapiPeer(null);

            eventLogWindow.append("JtapiPeer created successfully.\n");
        } catch (JtapiPeerUnavailableException e) {
            try {
                jtapiPeer = JtapiPeerFactory.getJtapiPeer("com.avaya.jtapi.tsapi.TsapiPeer");
                eventLogWindow.append("JtapiPeer created successfully.\n");
            } catch (JtapiPeerUnavailableException e2) {
                errorMessage = "JtapiPeerFactory.getJtapiPeer: caught " + "JtapiPeerUnavailableException\n";
                errorMessage.concat("Message: " + e2.getMessage() + "\n");
                errorMessage.concat("Error: JtapiPeer could not be created.  "
                        + "Verify your Jtapi client install.\n\n");

                eventLogWindow.append(errorMessage);

                return false;
            }
        }

        return true;
    }

    private synchronized boolean login() {
        String providerString = configurationSetting.getAESServiceName()
                + ";login=" + configurationSetting.getAESUserName()
                + ";passwd=" + configurationSetting.getAESUserPassword()
                + ";servers=" + configurationSetting.getAEServerAddress() + ":" + configurationSetting.getAEServerPort();

        if (jtapiPeer == null) {
            return false;
        }

        eventLogWindow.append("providerString = " + providerString + "\n");

        try {
            // create provider
            provider = jtapiPeer.getProvider(providerString);
            eventLogWindow.append("Provider created successfully.\n");
            eventLogWindow.append("Waiting for the provider to initialize...\n");

            // add a ProviderListener to the provider
            //provider.addProviderListener(providerListener);
            provider.addProviderListener(this);

            // wait to be notified when the provider is in service --
            // corresponding notify is in the providerChangedEvent() method
            wait();

            eventLogWindow.append("Provider is in service.\n");
            return true;
        } catch (Exception e) {
            errorMessage = "login() caught " + e + "\n";
            errorMessage.concat("Message: " + e.getMessage() + "\n\n");
            errorMessage.concat("Please verify that the login information is correct.\n\n");

            return false;
        }
    }

    @Action
    public void StartMonitor() {
        cmdStartMonitor.setEnabled(false);
        ApplicationLog.info("Starting AvayaLink Monitor");

//        // new
//        try {
//            if (initJtapi() == false) 
//                throw new Exception("initJtapi() returned FALSE");
//            if (login() == false) 
//                throw new Exception("login() returned FALSE");
//
//            // Setup heartbeat
//            try {
//                tsprovider = (ITsapiProviderEx) provider;            
//                tsprovider.setHeartbeatInterval((short) HEARTBEAT_INTERVAL);    // Set interval (in seconds)
//                eventLogWindow.append("Heartbeat interval set to " + HEARTBEAT_INTERVAL + " second(s)\n\n");                
//                lblHeartbeatText.setText("Server ID: " + tsprovider.getServerID());
//            } catch (Exception e) {
//                lblHeartbeatText.setText("ERROR: " + e.getMessage());
//                throw new Exception("Server ID: *ERROR*  (" + e.getMessage() + ")");                
//            }                       
//        } catch (Exception e) {
//            ApplicationLog.error(errorMessage);
//            
//            JOptionPane.showConfirmDialog(null,
//                "There was an ERROR in the AvayaLink StartMonitor subroutine.  (" +
//                        errorMessage + ")\n\nPlease correct error and re-start monitor.",
//                "AvayaLink Startup Error",
//                JOptionPane.OK_OPTION,
//                JOptionPane.ERROR_MESSAGE);            
//        } finally {
//            
//        }
                
        // old
        // Get jTapi
        eventLogWindow.append("Initializing Jtapi.\n");        
        if (initJtapi() == false) {
            //TODO:Review            
            ApplicationLog.error(errorMessage);
            ErrorHandler(errorMessage);

            JOptionPane.showMessageDialog(null,
                "There was an ERROR in the AvayaLink StartMonitor subroutine.  (" +
                    errorMessage + ")\n\nPlease correct error and re-start monitor.",
                "AvayaLink Startup Error",
                JOptionPane.ERROR_MESSAGE);

            cmdStartMonitor.setEnabled(true);
            return;
        }

        eventLogWindow.append("Logging in Provider.\n");
        // Get Provider
        if (login() == false) {
            //TODO:Review
            ApplicationLog.error(errorMessage);
            //ErrorHandler(errorMessage);
            
            JOptionPane.showMessageDialog(null,
                "ERROR during login() in StartMonitor subroutine.  Please correct error and re-start monitor.",
                "AvayaLink Start Error",
                JOptionPane.ERROR_MESSAGE);
            
            cmdStartMonitor.setEnabled(true);
            return;
        }
        
        // Setup heartbeat
        eventLogWindow.append("Setting up provider heatbeat.\n");
        try {
            tsprovider = (ITsapiProviderEx) provider;            
            tsprovider.setHeartbeatInterval((short) HEARTBEAT_INTERVAL);    // Set interval (in seconds)
            eventLogWindow.append("Heartbeat interval set to " + HEARTBEAT_INTERVAL + " second(s)\n");

            lblHeartbeatText.setText("Server ID: " + tsprovider.getServerID());
        } catch (Exception e) {
            lblHeartbeatText.setText("Server ID: *ERROR*  (" + e.getMessage() + ")");
        }
        
        // Setup timer task to keep pulling SMS stations.  We need to loop because the
        // phone type of a previously skipped extension could change or new stations
        // could be added to the Avaya switch that were not present during the first
        // scan when the program was initially run.
        eventLogWindow.append("Setting up SMS timer.\n");
        if (configurationSetting.isTestMode()) {
            smsTimer = new java.util.Timer();
            smsTimer.scheduleAtFixedRate(new RunBackgroundSMSMonitor(), 0, 90000);
        } else {
            smsTimer = new java.util.Timer();
            smsTimer.scheduleAtFixedRate(new RunBackgroundSMSMonitor(), 0, 90000);
        }
        
        // Setup timer task for Universe "keepalive"
        eventLogWindow.append("Starting Universe \"keep alive\" timer.\n");
        uvKeepAliveTimer = new java.util.Timer();
        uvKeepAliveTimer.scheduleAtFixedRate(new RunBackgroundUVKeepAlive(), 0, 90000);                        
        
        // Start socket server to listen for commands
        eventLogWindow.append("Starting socket command listener.\n");
        SocketServer socketServer = new SocketServer(configurationSetting, this, new SocketCommandProcessor());
        socketServer.start();        
    }

    @Override
    public void onSocketLogMessage(NewSocketLogMessageEvent event) {
        socketLogWindow.append(event.getMessage());
    }

    private void ErrorHandlerNew(String errorType, String errorMessage) {
        
    }
    
    private void ErrorHandler(String errorMessage) {
        eventLogWindow.append(errorMessage);        
        ApplicationLog.error(errorMessage);
        ErrorReportManager.reportErrorByEmail("AvayaLink ERROR", errorMessage);
    }

    private void ErrorHandler(String errorMessage, boolean shutdownFlag) {
        ErrorHandler(errorMessage);

        if (shutdownFlag) {
            ErrorReportManager.reportErrorByEmail("AvayaLink ERROR", errorMessage);
        }
    }

    private boolean AESReconnect() {
        boolean result = false;

        try {
            // Get jTapi
            if (initJtapi()) {
                // Get Provider
                if (login()) {
                    // Setup heartbeat                    
                    try {
                        tsprovider = (ITsapiProviderEx) provider;
                        tsprovider.setHeartbeatInterval((short) HEARTBEAT_INTERVAL);
                        lblHeartbeatText.setText("Server ID: " + tsprovider.getServerID());

                        result = true;
                    } catch (Exception e) {
                    }
                }
            }
        } catch (Exception e) {
        }

        return result;
    }
    
    private long GetIndexNumber(String fieldName) {
        long IndexNumber;
        int firstLeftBracket = fieldName.indexOf("[");
        int firstRightBracket = fieldName.indexOf("]");
        String tempValue = fieldName.substring(firstLeftBracket + 1,  firstRightBracket);
        IndexNumber = Long.parseLong(tempValue);        
        return IndexNumber;
    }

    private HashMap ParseSMSData(String[] smsResult) {
        HashMap resultArray = new HashMap();
        HashMap indexArray = new HashMap();
        
        for (int n = 0; n < smsResult.length; ++n) {
            String smsLine = smsResult[n];
            String[] fieldData = smsLine.split("=");
            String fieldName = fieldData[0].toUpperCase();
            long indexNumber = GetIndexNumber(fieldName);
            String fieldValue = "";
            try {
                fieldValue = fieldData[1];
            } catch (Exception e) {}
                            
            if (fieldName.startsWith("EXTENSION[")) {
                indexArray.put(String.valueOf(indexNumber), fieldValue);                                
                AvayaStationData stationData = new AvayaStationData();
                stationData.Extension = fieldValue;
                resultArray.put(fieldValue, stationData);
            } else {
                String extensionNumber = (String) indexArray.get(String.valueOf(indexNumber));
                AvayaStationData stationData = (AvayaStationData) resultArray.get(extensionNumber);
                AvayaStationData originalStationData = stationData;
                
                if (fieldName.startsWith("TYPE["))
                    stationData.PhoneType = fieldValue;
                else if(fieldName.startsWith("PORT["))
                    stationData.Port = fieldValue;
                else if(fieldName.startsWith("NAME["))
                    stationData.Name = fieldValue;
                else if(fieldName.startsWith("COVERAGE_PATH_1["))
                    stationData.CoveragePath1 = fieldValue;
                else if(fieldName.startsWith("COVERAGE_PATH_2["))
                    stationData.CoveragePath2 = fieldValue;
                else if(fieldName.startsWith("HUNT_TO_STATION["))
                    stationData.HuntToStation = fieldValue;
                else if(fieldName.startsWith("COR["))
                    stationData.COR = fieldValue;
                else if(fieldName.startsWith("COS["))
                    stationData.COS = fieldValue;                
                else if(fieldName.startsWith("ROOM["))
                    stationData.SiteRoomData = fieldValue;
                
                if (originalStationData != stationData)
                    resultArray.put(extensionNumber, stationData);
            }            
        }
                    
        return(resultArray);
    }

    private class RunBackgroundUVKeepAlive extends TimerTask implements Runnable {
        
        @Override
        public void run() {
            UVKeepAlive(configurationSetting);            
//            if (configurationSetting.isTestMode())
//                eventLogWindow.appendCommand("Executed UVKeepAlive() routine.\n", CommandType.SYSTEM, "");
        }        
    }
    
    private class RunBackgroundSMSMonitor extends TimerTask implements Runnable {

        @Override
        public void run() {
            if (AESServerOnline) {
                MonitorSMSExtensions();
                UpdateList();
            } else {
                eventLogWindow.appendCommand("Attempting reconnection to the AES server.\n", CommandType.SYSTEM, "");

                if (AESReconnect()) {
                    MonitorSMSExtensions();
                    UpdateList();
                } else {
                    eventLogWindow.appendCommand("The AES server is DOWN.  MonitorSMSExtensions() cancelled.\n", CommandType.SYSTEM, "");
                }
            }
        }
    }

    private void MonitorSMSExtensions() {
        if (GetStationExtensionsToMonitorUCB() && AESServerOnline) {
            AddStationListeners(smsStationExtensions);
        }
    }

    private void AddStationListeners(ConcurrentHashMap<String, AvayaStationData> stationTable) {
        Enumeration<String> htKeys = stationTable.keys();
        AvayaStationData avayaStationData;
        Thread aslThread = null;

        while (htKeys.hasMoreElements()) {
            try {
                // Key to hashmap is extension
                String htID = (String) htKeys.nextElement();

                // Check if extension is already in the hashmap.  If not, add.
                // If so, check to make sure terminal is still valid (not null)
                if (!extensionsBeingMonitored.containsKey(htID)) {
                    avayaStationData = (AvayaStationData) stationTable.get(htID);

                    AddStationListenerThread addStationListenerThread = new AddStationListenerThread();
                    addStationListenerThread.avayaStationData = avayaStationData;
                    aslThread = new Thread(addStationListenerThread);
                    aslThread.start();
                } else {
                    AvayaAgent avayaAgent;
                    avayaAgent = (AvayaAgent) extensionsBeingMonitored.get(htID);

                    // Check if we lost the address or terminal.  If so, re-add it.
                    if (avayaAgent.JTAPIAddress == null || avayaAgent.JTAPITerminal == null) {
                        // remove from table
                        extensionsBeingMonitored.remove(htID);

                        // re-add listener
                        avayaStationData = (AvayaStationData) stationTable.get(htID);

                        AddStationListenerThread addStationListenerThread = new AddStationListenerThread();
                        addStationListenerThread.avayaStationData = avayaStationData;
                        aslThread = new Thread(addStationListenerThread);
                        aslThread.start();
                    } else {
                        // Save original so we know if anything was updated
                        AvayaAgent originalAvayaAgent = avayaAgent;

                        // Check if the user's ability to manually dial has been changed
                        avayaStationData = (AvayaStationData) stationTable.get(htID);
                        String stationSiteValue = avayaStationData.SiteRoomData.toUpperCase();

                        if ((stationSiteValue.equals("CUBS") && avayaAgent.AllowManualDialing)
                                || (!stationSiteValue.equals("CUBS") && !avayaAgent.AllowManualDialing)) {
                            avayaAgent.AllowManualDialing = !avayaAgent.AllowManualDialing;
                        }

                        
                        // check if the extension is in the configuration settings to allow manual dialing
                        try {
                            if (avayaAgent.AllowManualDialing == false && configurationSetting.getManualDialAllowExtensions().contains(htID)) {
                                avayaAgent.AllowManualDialing = true;
                            }                            
                        } catch (Exception ee) {}

                        // Check if the AgentID has changed for the station
                        Agent[] agents = ((AgentTerminal) avayaAgent.JTAPITerminal).getAgents();
                        if (agents != null) {
                            avayaAgent.AgentID = agents[0].getAgentID();
                        } else {
                            avayaAgent.AgentID = "";
                        }

//                        String avayaAgentID = GetAgentID(avayaAgent.Extension);
//                        if (!avayaAgentID.equals(avayaAgent.AgentID)) {
//                            avayaAgent.AgentID = avayaAgentID;
//                        }

                        // Check if the name for the station has changed
                        if (!avayaStationData.Name.equals(avayaAgent.Name)) {
                            avayaAgent.Name = avayaStationData.Name;
                        }

                        // If updated, write to hash map
                        if (avayaAgent != originalAvayaAgent) {
                            extensionsBeingMonitored.put(htID, avayaAgent);
                        }
                    }
                }
            } catch (Exception e) {
                ErrorReportManager.reportErrorByEmail("AvayaLink AddStationListeners ERROR", "The AvayaLink software has encounted an exception in the AddStationListeners routine.  (" + e.getMessage() + ")\n");
            }

            // The connection to the AES server is gone.  Exit loop.
            if (!AESServerOnline) {
                return;
            }
        }
    }

    private class AddStationListenerThread implements Runnable {

        private AvayaStationData avayaStationData;

        @Override
        public void run() {
            AvayaAgent avayaAgent = new AvayaAgent();

            try {
                avayaAgent.Extension = avayaStationData.Extension;
                avayaAgent.AgentID = avayaStationData.AgentID;
                avayaAgent.Name = avayaStationData.Name;
                avayaAgent.Type = avayaStationData.PhoneType;
                avayaAgent.Port = avayaStationData.Port;

                if (avayaStationData.SiteRoomData.toUpperCase().equals("CUBS")) {
                    avayaAgent.AllowManualDialing = false;
                } else {
                    avayaAgent.AllowManualDialing = true;
                }

                // check if the extension is in the configuration settings to allow manual dialing
                try {
                    if (avayaAgent.AllowManualDialing == false && configurationSetting.getManualDialAllowExtensions().contains(avayaAgent.Extension))
                        avayaAgent.AllowManualDialing = true;
                } catch (Exception e) {}         

                // Get current timestamp.  This is used to verify if an agent
                // logs off of the phone system.
                Calendar calendar = Calendar.getInstance();
                java.util.Date now = calendar.getTime();
                avayaAgent.DateTimeAdded = new java.sql.Timestamp(now.getTime());

                // Avaya objects
                avayaAgent.JTAPIAddress = provider.getAddress(avayaAgent.Extension);
                avayaAgent.JTAPITerminal = provider.getTerminal(avayaAgent.Extension);                                                                                                   
                avayaAgent.JTAPITerminal.addCallListener(new CCCLAdapter());
                
                // Get Agent ID
                Agent[] agents = ((AgentTerminal) avayaAgent.JTAPITerminal).getAgents();
                if (agents != null) 
                    avayaAgent.AgentID = agents[0].getAgentID();
                
                // Write to hashmap of extensions we're monitoring
                extensionsBeingMonitored.put(avayaAgent.Extension, avayaAgent);
                
                // Write to hashmap Avaya Agent ID / Extension table
                if (avayaAgent.AgentID.equals(""))
                    avayaAgentIDs.put(avayaAgent.Extension, avayaAgent.Extension);
                else
                    avayaAgentIDs.put(avayaAgent.AgentID, avayaAgent.Extension);

                // Add to list box on screen                
                UpdateList();

                eventLogWindow.appendCommand("Added STATION extension# " + avayaAgent.Extension + "\n",
                        CommandType.REGISTER, avayaAgent.Extension);
            } catch (InvalidArgumentException | ResourceUnavailableException | MethodNotSupportedException e) {
                // Write to hashmap for extensions that errored out
                extensionsNotBeingMonitored.put(avayaAgent.Extension, avayaAgent.Extension);

                // Send notification email
                ErrorReportManager.reportErrorByEmail("AvayaLink AddStationListener ERROR x" + avayaAgent.Extension, "The AvayaLink software has encounted an error when adding a StationListener to extension x"
                        + avayaAgent.Extension + " (" + e.getMessage() + ")\n");
            }
        }
    }

    private class RemoveStationListenerThread implements Runnable {

        private String extensionNumber;

        @Override
        public void run() {
            CallListener[] cl;

            try {
                AvayaAgent avayaAgent = (AvayaAgent) extensionsBeingMonitored.get(extensionNumber);
                cl = avayaAgent.JTAPITerminal.getCallListeners();

                // Remove all listeners
                for (CallListener cl1 : cl) {
                    avayaAgent.JTAPITerminal.removeCallListener(cl1);
                }

                // Remove from list and update
                RemoveFromList(extensionNumber);

                // Remove from hash table
                extensionsBeingMonitored.remove(extensionNumber);

                eventLogWindow.appendCommand("Removed STATION extension# " + extensionNumber + "\n",
                        CommandType.DEREGISTER, extensionNumber);
            } catch (Exception e) {
                // Write to hashmap for extensions that errored out
                extensionsNotBeingMonitored.put(extensionNumber, extensionNumber);

                eventLogWindow.append("RemoveStationListenerThread *ERROR* for ext# " + extensionNumber
                        + " (" + e.getMessage().toString() + ")\n");
            }
        }
    }

    private boolean IsStationToMonitor(String extensionNumber, String phoneType, String portNumber, String stationRoom) {
        if (! stationRoom.toUpperCase().equals("CUBS"))
            return (false);
        
        // Check for invalid PBX port
        if (portNumber.toUpperCase().equals("X")) {
            return (false);
        }

        // Check if valid phone type at station
        if (!ValidPhoneType(phoneType)) {
            return (false);
        }

        // Check station selection criteria
        if (!configurationSetting.getStationSelection().toUpperCase().equals("ALL")) {
            if ((configurationSetting.getStationSelection().toUpperCase().equals("ROOM") && !stationRoom.toUpperCase().equals("CUBS"))) {
                return (false);
            }
        }

        // Check if test mode
        if (configurationSetting.isTestMode() && !configurationSetting.getDeveloperExtensions().contains(extensionNumber)) {
            return (false);
        }

        // No issues, okay to add
        return (true);
    }

    private boolean GetStationExtensionsToMonitor() {
        ModelChoices modelResults = null;
        ModelChoices modelChoices;
        StationType stationType;
        String extensionNumber;
        String phoneType;
        String portNumber;
        String stationRoom;

        extensionsNotBeingMonitoredCount = 0;
        smsStationExtensions.clear();

        eventLogWindow.appendCommand("Communicating with SMS for Station Extensions\n", CommandType.REGISTER, "");

        try {
            SMSRequest smsRequest = new SMSRequest(configurationSetting.getAEServerAddress(),
                configurationSetting.getCMUserName(), configurationSetting.getCMUserPassword());
                       
            // Create ModelFields Object
            objectFactory = new ObjectFactory();
            modelChoices = objectFactory.createModelChoices();
            stationType = objectFactory.createStationType();
            stationType.setExtension("");
            stationType.setName("");
            stationType.setType("");
            stationType.setPort("");
            stationType.setRoom("");
            modelChoices.getStation().add(stationType);

            smsRequest.execRequest(modelChoices, "list", "");
            modelResults = smsRequest.getData();
            smsRequest.releaseSession();

            eventLogWindow.appendCommand("SMS Communication completed.\n", CommandType.REGISTER, "");
        } catch (Exception e) {
            ErrorReportManager.reportErrorByEmail("AvayaLink ERROR", "There was an exception in the GetStationExtensionsToMonitor() routine.  (" + e.getMessage() + ")");
            return (false);
        }

        if (modelResults == null) {
            ErrorReportManager.reportErrorByEmail("AvayaLink Warning", "No data returned for modelResults in GetStationExtensionsToMonitor() routine.");
            return (false);
        }

        for (int t = 0; t < modelResults.getStation().size(); t++) {
            extensionNumber = modelResults.getStation().get(t).getExtension();
            phoneType = modelResults.getStation().get(t).getType();
            portNumber = modelResults.getStation().get(t).getPort();
            stationRoom = modelResults.getStation().get(t).getRoom();

            if (IsStationToMonitor(extensionNumber, phoneType, portNumber, stationRoom)) {
                if (!smsStationExtensions.containsKey(extensionNumber)) {
                    AvayaStationData avayaStationData = new AvayaStationData();

                    avayaStationData.Extension = extensionNumber;
                    //avayaStationData.AgentID = GetAgentID(extensionNumber);
                    avayaStationData.Name = modelResults.getStation().get(t).getName();
                    avayaStationData.SiteRoomData = modelResults.getStation().get(t).getRoom();
                    avayaStationData.Port = portNumber;
                    avayaStationData.PhoneType = phoneType;

                    // Add to hash table
                    smsStationExtensions.put(extensionNumber, avayaStationData);
                }
            } else {
                extensionsNotBeingMonitoredCount++;

                // Check if invalid phone type extension WAS valid and in our table.  If so, remove it
                // as the phone type must have been changed.
                if (extensionsBeingMonitored.containsKey(extensionNumber)) {
                    eventLogWindow.appendCommand("REMOVING x" + extensionNumber + " AS PHONE TYPE/PORT/ROOM (" + phoneType + ", " + portNumber + ", " + stationRoom + ") IS NOW INVALID\n",
                            CommandType.DEREGISTER, extensionNumber);

                    // Remove station listener                            
                    RemoveStationListenerThread removeStationListenerThread = new RemoveStationListenerThread();
                    removeStationListenerThread.extensionNumber = extensionNumber;
                    Thread rslThread = new Thread(removeStationListenerThread);
                    rslThread.start();
                } else {
                    eventLogWindow.appendCommand("SKIPPING STATION: " + phoneType + ", PORT: " + portNumber + ", ROOM: " + stationRoom + "\n",
                            CommandType.REGISTER, extensionNumber);
                }
            }
        }

        return (true);
    }

    private boolean GetStationExtensionsToMonitorUCB() {
        String[] smsResult = null;
        ModelChoices modelResults = null;
        ModelChoices modelChoices;
        StationType stationType;
        String extensionNumber;
        String phoneType;
        String portNumber;
        String stationRoom;

        extensionsNotBeingMonitoredCount = 0;
        smsStationExtensions.clear();

        eventLogWindow.appendCommand("Communicating with SMS for Station Extensions\n", CommandType.REGISTER, "");

        try {
            SMSRequestUCB smsRequest = new SMSRequestUCB(configurationSetting.getAEServerAddress(),
                configurationSetting.getCMUserName(), configurationSetting.getCMUserPassword());
                       
            // Create ModelFields Object
            objectFactory = new ObjectFactory();
            modelChoices = objectFactory.createModelChoices();
            stationType = objectFactory.createStationType();
            stationType.setExtension("");
            stationType.setName("");
            stationType.setType("");
            stationType.setPort("");
            stationType.setRoom("");
            modelChoices.getStation().add(stationType);

            smsRequest.execRequest(modelChoices, "list", "");
            //modelResults = smsRequest.getData();
            smsResult = smsRequest.getReturnData();
            smsRequest.releaseSession();

            eventLogWindow.appendCommand("SMS Communication completed.\n", CommandType.REGISTER, "");
        } catch (Exception e) {
            ErrorReportManager.reportErrorByEmail("AvayaLink ERROR", "There was an exception in the GetStationExtensionsToMonitor() routine.  (" + e.getMessage() + ")");
            return (false);
        }

        if (smsResult == null) {
            ErrorReportManager.reportErrorByEmail("AvayaLink Warning", "No data returned for modelResults in GetStationExtensionsToMonitor() routine.");
            return (false);
        }
        
        HashMap<String, AvayaStationData> smsResultArray = ParseSMSData(smsResult);
        
        for(Entry<String, AvayaStationData> entry : smsResultArray.entrySet()) {
            extensionNumber = entry.getKey();
            AvayaStationData avayaStationDataTable = (AvayaStationData) entry.getValue();                       
            phoneType = avayaStationDataTable.PhoneType;
            portNumber = avayaStationDataTable.Port;
            stationRoom = avayaStationDataTable.SiteRoomData;
        
            if (IsStationToMonitor(extensionNumber, phoneType, portNumber, stationRoom)) {
                if (!smsStationExtensions.containsKey(extensionNumber)) {
                    AvayaStationData avayaStationData = avayaStationDataTable;
                    smsStationExtensions.put(extensionNumber, avayaStationData);
                }
            } else {
                extensionsNotBeingMonitoredCount++;

                // Check if invalid phone type extension WAS valid and in our table.  If so, remove it
                // as the phone type must have been changed.
                if (extensionsBeingMonitored.containsKey(extensionNumber)) {
                    eventLogWindow.appendCommand("REMOVING x" + extensionNumber + " AS PHONE TYPE/PORT/ROOM (" + phoneType + ", " + portNumber + ", " + stationRoom + ") IS NOW INVALID\n",
                            CommandType.DEREGISTER, extensionNumber);

                    // Remove station listener                            
                    RemoveStationListenerThread removeStationListenerThread = new RemoveStationListenerThread();
                    removeStationListenerThread.extensionNumber = extensionNumber;
                    Thread rslThread = new Thread(removeStationListenerThread);
                    rslThread.start();
                } else {
                    eventLogWindow.appendCommand("SKIPPING STATION: " + phoneType + ", PORT: " + portNumber + ", ROOM: " + stationRoom + "\n",
                            CommandType.REGISTER, extensionNumber);
                }
            }
        }
        
        return (true);
    }
    
    private String GetStationAgentID(String extensionNumber) {
        AvayaAgent avayaAgent;
        AgentTerminal agentTerminal;
        Agent terminalAgents[];
        Agent terminalAgent;

        String stationAgentID = null;

        try {
            avayaAgent = (AvayaAgent) extensionsBeingMonitored.get(extensionNumber);
            agentTerminal = (AgentTerminal) avayaAgent.JTAPITerminal;
            terminalAgents = agentTerminal.getAgents();
            terminalAgent = terminalAgents[0];
            stationAgentID = terminalAgent.getAgentID();
        } catch (Exception e) {
            ErrorReportManager.reportErrorByEmail("AvayaLink ERROR", "There was an exception in the GetStationAgentID routine.  (" + e.getMessage() + ")");
        }

        return stationAgentID;
    }

    private class GetAgentExtensionThread implements Runnable {        
        public String avayaAgentID;
        public PrintWriter clientSocket = this.clientSocket;
        private String avayaStationID = null;

        @Override
        public void run() {
            int resultCode;
            String resultText;
            
            // Search hashmap for extension
            if (extensionsBeingMonitored.containsKey(avayaAgentID)) {
                avayaStationID = avayaAgentID;
            } else {
                ConcurrentHashMap<String, AvayaAgent> selects = extensionsBeingMonitored;  
                for(Entry<String, AvayaAgent> entry : selects.entrySet()) {
                    String key = entry.getKey();
                    AvayaAgent avayaAgent = entry.getValue();                
                    if (avayaAgent.AgentID.equals(avayaAgentID)) {
                        avayaStationID = key;
                        break;
                    }
                }
            }
                                   
            if (avayaStationID == null) {
                resultCode = -1;
                resultText = avayaAgentID + " RETURNED NULL IN GetAgentExtensionThread";
            } else {
                if (avayaStationID.isEmpty()) {
                    resultCode = -1;
                    resultText = avayaAgentID + " IS UNSTAFFED OR INVALID";
                } else {
                    resultCode = 0;
                    resultText = avayaStationID;
                }            
            }

            // Send response to socket
            clientSocket.println(resultCode + SOCKET_FIELD_DELIMITER + resultText);
            clientSocket.flush();
            clientSocket.close();
        }
    }

    private boolean ValidPhoneType(String phoneType) {
        phoneType = phoneType.trim().toUpperCase();

        if (phoneType.equals("VIRTUAL")) {
            return false;
        } else if (phoneType.equals("DS1FD")) {
            return false;
        } else if (phoneType.equals("DMCC")) {
            return false;
        } else if (phoneType.equals("XMOBILE")) {
            return false;
        } else if (phoneType.equals("2500")) {
            return false;
        } else if (phoneType.equals("8110")) {
            return false;
        } else if (phoneType.equals("6408") && configurationSetting.isTestMode()) {
            return false;
        } else {
            return true;
        }
    }
    MouseListener mouseListener = new MouseAdapter() {

        @Override
        public void mousePressed(MouseEvent mouseEvent) {
            int modifiers = mouseEvent.getModifiers();

            if ((modifiers & InputEvent.BUTTON3_MASK) == InputEvent.BUTTON3_MASK) {
                check(mouseEvent);
            }
        }

        @Override
        public void mouseReleased(MouseEvent mouseEvent) {
            if (SwingUtilities.isRightMouseButton(mouseEvent)) {
                check(mouseEvent);
            }
        }

        public void check(MouseEvent e) {
            if (e.isPopupTrigger()) {
                //if the event shows the menu, select the item
                lstExtensionsBeingMonitored.setSelectedIndex(lstExtensionsBeingMonitored.locationToIndex(e.getPoint()));

                //and show the menu
                popExtensionsBeingMonitored.show(lstExtensionsBeingMonitored, e.getX(), e.getY());
            }
        }
    };

    private void UpdateList() {
        SwingUtilities.invokeLater(new Runnable() {

            public void run() {
                Collection<String> objects = extensionsBeingMonitored.keySet();
                Calendar calendar = Calendar.getInstance();
                java.util.Date now = calendar.getTime();
                int[] selectedListItems;

                // Save user's selected list entries
                selectedListItems = lstExtensionsBeingMonitored.getSelectedIndices();

                sortedExtensionList.clear();

                for (Object o : objects) {
                    sortedExtensionList.add(o);
                }

                lstExtensionsBeingMonitored.setModel(sortedExtensionList);

                extensionsBeingMonitoredCount = sortedExtensionList.getSize();
                extensionsMonitorErrorCount = extensionsNotBeingMonitored.size();

                lblExtensionsBeingMonitored.setText("Stations monitored: " + extensionsBeingMonitoredCount
                        + ", (" + extensionsNotBeingMonitoredCount + " stations NOT monitored, "
                        + extensionsMonitorErrorCount + " listener errors)"
                        + "  Last updated: " + now.toString() + "\n");

                // Reset user's selected entries
                lstExtensionsBeingMonitored.setSelectedIndices(selectedListItems);
            }
        });
    }

    private void RemoveFromList(String extensionNumber) {
        sortedExtensionList.removeElement(extensionNumber);
        UpdateList();
    }

    private synchronized void handleProviderInService() {
        notify();
    }

    private class CCCLAdapter extends CallControlConnectionListenerAdapter {
        @Override
        public void connectionAlerting(CallControlConnectionEvent arg0) {
            final CallControlConnectionEvent event = arg0;
            String AvayaDeviceID;
            String callingAddress;
            String calledAddress;

            try {
                AvayaDeviceID = event.getConnection().getAddress().getName();
                if (!extensionsBeingMonitored.containsKey(AvayaDeviceID)) 
                    return;                
                callingAddress = event.getCallingAddress().getName();
                calledAddress = event.getCalledAddress().getName();
            } catch (Exception npe) {                
                return;
            }

            DBClasses dbc = new DBClasses();
            String phoneNumber;
            String extensionNumber;

            if (callingAddress.length() == EXTENSIONLENGTH && calledAddress.length() >= 7) {
                extensionNumber = callingAddress;
                phoneNumber = dbc.appendDefaultAreaCode(calledAddress);
            } else if (callingAddress.length() >= 7 && calledAddress.length() == EXTENSIONLENGTH) {
                extensionNumber = calledAddress;
                phoneNumber = dbc.appendDefaultAreaCode(callingAddress);
            } else {
                return;
            }

            eventLogWindow.appendCommand("[" + extensionNumber + "] of call from [" + phoneNumber + "]\n",
                CommandType.ALERTING, AvayaDeviceID);
        }

        @Override
        public void connectionEstablished(CallControlConnectionEvent arg0) {

            final CallControlConnectionEvent event = arg0;

            new Thread("connectionEstablished") {                            
                @Override
                public void run() {
                    if (event.getCause() != CAUSE_NORMAL)
                        return;
                    
                    LucentV5CallInfo lv5CallInfo = (LucentV5CallInfo) event.getCall();
                    String callUCID = "";
                    try {
                        callUCID = lv5CallInfo.getUCID();
                    } catch (Exception e) {
                        return;
                    }
                                                            
                    String AvayaDeviceID;
                    String callingAddress;
                    String calledAddress;
                    
                    try {
                        AvayaDeviceID = event.getConnection().getAddress().getName();
                        if (! extensionsBeingMonitored.containsKey(AvayaDeviceID))
                            return;                                    
                        callingAddress = event.getCallingAddress().getName();
                        calledAddress = event.getCalledAddress().getName();
                    } catch (Exception npe) {
                        return;
                    }
                                                       
                    DBClasses dbc = new DBClasses();
                    String phoneNumber;
                    String extensionNumber;
                    boolean inboundCall = false;
                    boolean outboundCall = false;                                        
                    
                    if (callingAddress.length() == EXTENSIONLENGTH && calledAddress.length() >= 7 ) {
                        extensionNumber = callingAddress;
                        phoneNumber = dbc.appendDefaultAreaCode(calledAddress);
                        
                        outboundCall = true;
                    } else if (callingAddress.length() >= 7 && calledAddress.length() == EXTENSIONLENGTH) {
                        extensionNumber = calledAddress;
                        phoneNumber = dbc.appendDefaultAreaCode(callingAddress);
                        
                        inboundCall = true;                        
                    } else {
                        return;
                    }

                    AvayaAgent avayaAgent = (AvayaAgent) extensionsBeingMonitored.get(AvayaDeviceID);
                    if (avayaAgent == null) 
                        return;                

                    if (callUCID.equals(avayaAgent.LastUCIDConnected)) {
                        return;     // We've already checked this call.  Nothing to do.
                    } else {
                        avayaAgent.LastUCIDConnected = callUCID;
                        extensionsBeingMonitored.put(AvayaDeviceID, avayaAgent);
                    }

                    // Show event to log                
                    if (inboundCall) {
                        eventLogWindow.appendCommand("INBOUND CALL from [" + phoneNumber + "]\n",
                            CommandType.CONNECT, AvayaDeviceID);
                    } else {
                        eventLogWindow.appendCommand("[x" + extensionNumber + "] to [" + phoneNumber + "], UCID: " + callUCID + "\n",
                            CommandType.CONNECT, AvayaDeviceID);
                    }
                    
                    // Check phone number is in DND Table.  If so, abort call and transfer to warning extension.                
                    boolean DNDViolation = false;                    
                    if (outboundCall && configurationSetting.getIsDNDChecking() && !configurationSetting.getDNDWarningExtension().isEmpty()) {                                               
                        try {
                            if (dbc.FoundInDNDTable(phoneNumber)) {
                                DNDViolation = true;

                                // Phone is in DND table.
                                eventLogWindow.appendCommand("[x" + avayaAgent.Extension + "] to [" + phoneNumber + "] *DND* phone number!\n",
                                    CommandType.DND, avayaAgent.Extension);

                                // Write to Cubs_DNDHits table.
                                try {
                                    dbc.WriteDNDRecord("", "", avayaAgent.Extension, phoneNumber);
                                } catch (Exception e) {
                                    eventLogWindow.appendCommand("[x" + avayaAgent.Extension + "] to [" + phoneNumber
                                        + "] CANNOT WRITE DND HIT RECORD TO DATABASE.  (" + e.getMessage() + ")\n",
                                        CommandType.ERROR, avayaAgent.Extension);
                                }

                                // Transfer call to DND warning extension message.
                                if (TRANSFERDNDCALLS) {
                                    try {
                                        DialDNDWarningThread dialDNDWarningThread = new DialDNDWarningThread(avayaAgent);
                                        Thread dwThread = new Thread(dialDNDWarningThread);
                                        dwThread.start();
                                    } catch (Exception e) {
                                        eventLogWindow.appendCommand("[x" + avayaAgent.Extension + "] to [" + avayaAgent.Extension
                                            + "] Error on DND warning message transfer to " + configurationSetting.getDNDWarningExtension() + " (" + e.getMessage() + ")\n",
                                            CommandType.ERROR, avayaAgent.Extension);
                                    }
                                }
                            }
                        } catch (Exception e) {
                            eventLogWindow.appendCommand("[x" + avayaAgent.Extension + "] to [" + phoneNumber
                                + "] CANNOT SEARCH DND DATABASE.  (" + e.getMessage() + ")\n",
                                CommandType.ERROR, avayaAgent.Extension);
                        }
                    }
 
                    // Check if outbound call was manually dialed.
                    boolean ManualDialViolation = false;                    
                    if (outboundCall && !DNDViolation) {
                        if (!avayaAgent.AllowManualDialing && !avayaAgent.CurrentUCID.equals(callUCID) && !avayaAgent.LastUCIDAlerted.equals(callUCID)) {
                            if (TRANSFERMANUALCALLS && !chkAllowManualDialing.isSelected()) {
                                ManualDialViolation = true;

                                eventLogWindow.appendCommand("MANUAL DIAL [" + phoneNumber + "]\n", CommandType.WARNING, extensionNumber);

                                DialNoManualDialingWarningThread dialNoManualDialingWarningThread = new DialNoManualDialingWarningThread(avayaAgent);
                                Thread dwThread = new Thread(dialNoManualDialingWarningThread);
                                dwThread.start();
                            }
                        }
                    }
                                                            
                    // Log new call                
                    if (LOGCALLS) {                                              
                        AvayaCall avayaCall = new AvayaCall();
                        try {
                            avayaCall = currentAvayaCalls.get(avayaAgent.CurrentUCID);
                            avayaCall.AvayaCallUCID = callUCID;
                        } catch (Exception ex) {
                            return;
                        }
                                    
                        if (outboundCall) 
                            avayaCall.CallType = "O"; // Outbound
                        else
                            avayaCall.CallType = "I"; // Inbound
                        avayaCall.ExtensionNumber = AvayaDeviceID;
                        avayaCall.PhoneNumber = phoneNumber;                        
                        avayaCall.CallStart = new Timestamp(Calendar.getInstance().getTimeInMillis());
                        avayaCall.DNDViolation = DNDViolation;
                        avayaCall.ManualDialViolation = ManualDialViolation;                    
                        currentAvayaCalls.put(callUCID, avayaCall);
                        
                        // Write inbound call file to let CUBS know this extension 
                        // answered an inbound call.
//                        if (inboundCall) {
//                            String textToWrite = avayaCall.ExtensionNumber + "|";
//                            textToWrite = textToWrite + avayaCall.PhoneNumber + "|";
//                            textToWrite = textToWrite + avayaCall.CallStart.toString() + "|";
//                            textToWrite = textToWrite + avayaCall.SocketMessageReceived;
//                            
//                            if (!writeInboundCall("INBOUND." + avayaCall.AvayaCallUCID, textToWrite)) {
//                                ErrorReportManager.reportErrorByEmail("AvayaLink ERROR", "The writeInboundCall routine returned FALSE.");
//                            }                            
//                        }
                    }
                }
            }
            .start();
        }
        
        @Override
        public void connectionDisconnected(CallControlConnectionEvent arg0) {                        
            final CallControlConnectionEvent event = arg0;                        
            LucentV5CallInfo lv5CallInfo = (LucentV5CallInfo) event.getCall();
            String callUCID;
            AvayaAgent avayaAgent;
            String AvayaDeviceID;
                                               
            try {
                AvayaDeviceID = event.getConnection().getAddress().getName();
                if (! extensionsBeingMonitored.containsKey(AvayaDeviceID))
                    return;    
                avayaAgent = (AvayaAgent) extensionsBeingMonitored.get(AvayaDeviceID);
                callUCID = lv5CallInfo.getUCID();            
            } catch (Exception npe) {
                return;
            }
                                                                                                              
            if (callUCID.equals(avayaAgent.LastUCIDDisconnected)) {
                return;     // We've already checked this call.  Nothing to do.
            } else {
                avayaAgent.LastUCIDDisconnected = callUCID;
                extensionsBeingMonitored.put(AvayaDeviceID, avayaAgent);
            }

            // Log end of call to currentAvayaCalls
            if (LOGCALLS) {
                AvayaCall avayaCall = (AvayaCall) currentAvayaCalls.get(callUCID);
                if (avayaCall != null) {
                    // Check if the call was a DND or a manual dial violation.  If so, set custom failure code.
                    if (avayaCall.FailureCode.equals("")) {
                        if (avayaCall.DNDViolation) {
                            avayaCall.FailureCode = "DND";
                        } else if (avayaCall.ManualDialViolation) {
                            avayaCall.FailureCode = "MDV";
                        }
                    }
                    avayaCall.CallEnd = new Timestamp(Calendar.getInstance().getTimeInMillis());
                    
                    CallLogRecord callLogRecord = new CallLogRecord();                    
                    callLogRecord.LogonName = avayaCall.CUBSLogonName;
                    callLogRecord.AvayaUCID = avayaCall.AvayaCallUCID;
                    callLogRecord.ExtensionNumber = avayaCall.ExtensionNumber;
                    callLogRecord.PhoneNumber = avayaCall.PhoneNumber;
                    callLogRecord.CallStartTime = avayaCall.CallStart.toString();
                    callLogRecord.CallEndTime = avayaCall.CallEnd.toString();
                    callLogRecord.FailureCode = avayaCall.FailureCode;
                    callLogRecord.CallType = avayaCall.CallType;
                    callLogRecord.SocketMessageReceived = avayaCall.SocketMessageReceived;

                    try {
                        UpdateCUBSCallLog(configurationSetting, callLogRecord);
                    } catch (Exception e) {
                        ErrorReportManager.reportErrorByEmail("AvayaLink ERROR", "The writeCallOutcome routine returned FALSE.");
                    }
                                       
                    // Remove from currentAvayaCalls
                    currentAvayaCalls.remove(avayaCall.AvayaCallUCID);
                    
                    // Show event on log
                    eventLogWindow.appendCommand("[x" + AvayaDeviceID + "] from ["
                        + callLogRecord.PhoneNumber
                        + "], UCID: " + callUCID + "\n",
                        CommandType.DISCONNECT,
                        AvayaDeviceID);
                } else {
                    // NOT an AvayaLink call, but show on the log anyway
                    String phoneNumber = "(empty)";
                    try {                      
                        // Show event on log
                        phoneNumber = event.getCalledAddress().getName();
                    } catch (Exception e) {}
                    
                    eventLogWindow.appendCommand("[x" + AvayaDeviceID + "] from ["                        
                        + phoneNumber
                        + "], UCID: " + callUCID + "\n",
                        CommandType.DISCONNECT,
                        AvayaDeviceID);                                                           
                }
            }
        }
        
        @Override
        public void connectionFailed(CallControlConnectionEvent arg0) {
            final CallControlConnectionEvent event = arg0;
            String connectionName;
            String callingAddress;
            String calledAddress;
            int failureCode;

            try {
                failureCode = arg0.getCallControlCause();
                connectionName = arg0.getCallingAddress().getName();
                if (!extensionsBeingMonitored.containsKey(connectionName)) 
                    return;
               
                callingAddress = arg0.getCallingAddress().getName();
                calledAddress = arg0.getCalledAddress().getName();
            } catch (Exception npe) {
                // TODO: V3 log
                return;
            }

            String failureReason;
            DBClasses dbc = new DBClasses();
            String phoneNumber;
            String extensionNumber;

            if (callingAddress.length() == EXTENSIONLENGTH) {
                extensionNumber = callingAddress;
                phoneNumber = dbc.appendDefaultAreaCode(calledAddress);
            } else if (callingAddress.length() >= 7 && calledAddress.length() == EXTENSIONLENGTH) {
                extensionNumber = calledAddress;
                phoneNumber = dbc.appendDefaultAreaCode(callingAddress);
            } else {
                return;
            }
            
            // Get call UCID and append failure code
            LucentV5CallInfo lv5CallInfo;
            String callUCID;            
            try {
                lv5CallInfo = (LucentV5CallInfo) arg0.getCall();
                callUCID = lv5CallInfo.getUCID();            
            } catch (Exception e) {
                return;
            }
            if (callUCID == null) {
                return;
            } else {
                // Log failure code to currentAvayaCalls
                if (LOGCALLS) {
                    AvayaCall avayaCall = (AvayaCall) currentAvayaCalls.get(callUCID);
                    if (avayaCall != null) {
                        if (avayaCall.AvayaCallUCID == null) {
                            avayaCall.AvayaCallUCID = callUCID;                           
                            avayaCall.CallType = "O"; // Outbound
                            avayaCall.ExtensionNumber = event.getConnection().getAddress().getName();
                            avayaCall.PhoneNumber = phoneNumber;                        
                            avayaCall.CallStart = new Timestamp(Calendar.getInstance().getTimeInMillis());
                            avayaCall.DNDViolation = false;
                            avayaCall.ManualDialViolation = false;                    
                        }                        
                        avayaCall.FailureCode = Integer.toString(failureCode);
                        currentAvayaCalls.put(avayaCall.AvayaCallUCID, avayaCall);
                    }
                }
            }

            switch (failureCode) {
                case CallControlEvent.CAUSE_NORMAL:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CAUSE_NORMAL\n";
                    break;
                case CallControlEvent.CAUSE_UNKNOWN:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CAUSE_UNKNOWN\n";
                    break;
                case CallControlEvent.CAUSE_CALL_CANCELLED:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CAUSE_CALL_CANCELLED\n";
                    break;
                case CallControlEvent.CAUSE_DEST_NOT_OBTAINABLE:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CAUSE_DEST_NOT_OBTAINABLE\n";
                    break;
                case CallControlEvent.CAUSE_INCOMPATIBLE_DESTINATION:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CAUSE_INCOMPATIBLE_DESTINATION\n";
                    break;
                case CallControlEvent.CAUSE_LOCKOUT:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CAUSE_LOCKOUT\n";
                    break;
                case CallControlEvent.CAUSE_NEW_CALL:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CAUSE_NEW_CALL\n";
                    break;
                case CallControlEvent.CAUSE_RESOURCES_NOT_AVAILABLE:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CAUSE_RESOURCES_NOT_AVAILABLE\n";
                    break;
                case CallControlEvent.CAUSE_NETWORK_CONGESTION:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CAUSE_NETWORK_CONNECTION\n";
                    break;
                case CallControlEvent.CAUSE_NETWORK_NOT_OBTAINABLE:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CAUSE_NETWORK_NOT_AVAILABLE\n";
                    break;
                case CallControlEvent.CAUSE_SNAPSHOT:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CAUSE_SNAPSHOT\n";
                    break;
                case CallControlEvent.CAUSE_ALTERNATE:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: ALTERNATE\n";
                    break;
                case CallControlEvent.CAUSE_BUSY:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: BUSY\n";
                    break;
                case CallControlEvent.CAUSE_CALL_BACK:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CALL_BACK\n";
                    break;
                case CallControlEvent.CAUSE_CALL_NOT_ANSWERED:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CALL_NOT_ANSWERED\n";
                    break;
                case CallControlEvent.CAUSE_CALL_PICKUP:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CALL_PICKUP\n";
                    break;
                case CallControlEvent.CAUSE_CONFERENCE:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: CONFERENCE\n";
                    break;
                case CallControlEvent.CAUSE_DO_NOT_DISTURB:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: DO_NOT_DISTURB\n";
                    break;
                case CallControlEvent.CAUSE_PARK:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: PARK\n";
                    break;
                case CallControlEvent.CAUSE_REDIRECTED:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: REDIRECTED\n";
                    break;
                case CallControlEvent.CAUSE_REORDER_TONE:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: REORDER_TONE\n";
                    break;
                case CallControlEvent.CAUSE_TRANSFER:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: TRANSFER\n";
                    break;
                case CallControlEvent.CAUSE_TRUNKS_BUSY:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: TRUNKS_BUSY\n";
                    break;
                case CallControlEvent.CAUSE_UNHOLD:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: UNHOLD\n";
                    break;
                default:
                    failureReason = "[x" + extensionNumber + "] to [" + phoneNumber + "] Reason: UNKNOWN (Failure Code: " + failureCode + ")\n";
                    break;
            }

            eventLogWindow.appendCommand(failureReason,
                    CommandType.FAILURE, connectionName);

            // Disconnect call if it's the only connection.   
            AvayaAgent avayaAgent = (AvayaAgent) extensionsBeingMonitored.get(connectionName);
            int NumberOfConnections = avayaAgent.JTAPITerminal.getAddresses().length;
            if (avayaAgent != null && NumberOfConnections == 1) {
                // Only disconnect the connection if it's the only one (no one on hold)
                try {                
                    Thread.sleep(2500);  // user delay 
                } catch (InterruptedException ex) {}

                HangupPhoneNumberThread hangupPhoneNumberThread = new HangupPhoneNumberThread(null, avayaAgent);
                Thread hupThread = new Thread(hangupPhoneNumberThread);
                hupThread.start();
            }
        }

        @Override
        public void connectionUnknown(CallControlConnectionEvent arg0) {
            int failureCode;
            String dialingExtension;
            String numberDialed;

            try {
                failureCode = arg0.getCallControlCause();
                dialingExtension = arg0.getCallingAddress().getName();
                numberDialed = arg0.getCalledAddress().getName();

                ValidatePhoneNumber validatePhone = new ValidatePhoneNumber();
                numberDialed = validatePhone.appendDefaultAreaCode(numberDialed);
            } catch (NullPointerException npe) {
                return;
            } catch (Exception e) {
                e.printStackTrace();
                ErrorReportManager.reportErrorByEmail("AvayaLink ERROR", "There was an exception in the connectionUnknown routine.  (" + e.getMessage() + ")");
                return;
            }

            eventLogWindow.appendCommand("[x" + dialingExtension + "] to [" + numberDialed + "] Reason: UnknownFailure Code: " + failureCode + ")\n",
                    CommandType.UNKNOWN, dialingExtension);
        }
    }

    private class DialDNDWarningThread implements Runnable {

        private final AvayaAgent avayaAgent;

        public DialDNDWarningThread(AvayaAgent avayaAgent) {
            this.avayaAgent = avayaAgent;
        }

        @Override
        public void run() {
            Terminal terminal;
            Address address;
            LucentCallEx2 myCall;

            try {
                terminal = avayaAgent.JTAPITerminal;
                address = avayaAgent.JTAPIAddress;

                // Hangup call
                disconnect(terminal.getTerminalConnections());

                // Connect call to DND warning message
                myCall = (LucentCallEx2) provider.createCall();
                myCall.fastConnect(terminal, address, configurationSetting.getDNDWarningExtension(), false, null, null);
            } catch (Exception e) {
                eventLogWindow.appendCommand("Failed to connect x" + avayaAgent.Extension + " to "
                        + configurationSetting.getDNDWarningExtension() + "(" + e.getMessage() + ")\n", CommandType.DND, "");
            }
        }
    }

    private class DialNoManualDialingWarningThread implements Runnable {

        private AvayaAgent avayaAgent;

        public DialNoManualDialingWarningThread(AvayaAgent avayaAgent) {
            this.avayaAgent = avayaAgent;
        }

        public void run() {
            Terminal terminal;
            Address address;
            LucentCallEx2 myCall;

            try {
                terminal = avayaAgent.JTAPITerminal;
                address = avayaAgent.JTAPIAddress;
                //extensionNumber = avayaAgent.Extension;

                // Hangup call
                disconnect(terminal.getTerminalConnections());

                // Connect call to No Manual Dialing warning message
                myCall = (LucentCallEx2) provider.createCall();
                myCall.fastConnect(terminal, address, configurationSetting.getManualDialWarningExtension(), false, null, null);
            } catch (Exception e) {
                //BUGFIX
                e.printStackTrace();
                ErrorReportManager.reportErrorByEmail("AvayaLink *DEBUG* ERROR", "There was an exception in the DialNoManualDialingWarningThread routine.  (" + e.getStackTrace().toString() + ")");
                //BUGFIX

                eventLogWindow.appendCommand("Failed to connect x" + this.avayaAgent.Extension + " to "
                        + configurationSetting.getManualDialWarningExtension() + " (" + e.getMessage() + ")\n",
                        CommandType.ERROR, "");
            }
        }
    }

    private class DialPhoneNumberThread implements Runnable {
        private final PrintWriter clientDialSocket;
        private final AvayaAgent avayaAgent;
        private final String CUBSLogonName;
        private final String phoneNumber;
        private final String socketMessageReceived;
        int resultCode = 0;
        String resultText = "";

        public DialPhoneNumberThread(PrintWriter clientSocket, AvayaAgent avayaAgent, String phoneNumber, String socketMessageReceived) {
            this.clientDialSocket = clientSocket;
            this.avayaAgent = avayaAgent;
            this.phoneNumber = phoneNumber;
            this.CUBSLogonName = socketMessageReceived.split("~")[3];
            this.socketMessageReceived = socketMessageReceived;
        }

        @Override
        public void run() {
            Terminal terminal = avayaAgent.JTAPITerminal;
            Address address = avayaAgent.JTAPIAddress;
            String extensionNumber = avayaAgent.Extension;

            try {
                // dial phone number
                LucentCallEx2 myCall = (LucentCallEx2) provider.createCall();
                UserToUserInfo uui = new UserToUserInfo("AVAYALINK:" + socketMessageReceived);               
                myCall.fastConnect(terminal, address, phoneNumber, false, uui, "");

                LucentV5CallInfo lv5CallInfo = (LucentV5CallInfo) myCall;
                avayaAgent.CurrentUCID = lv5CallInfo.getUCID();

                resultCode = 0;
                resultText = "UCID:" + avayaAgent.CurrentUCID;
                
                AvayaCall avayaCall = new AvayaCall();
                avayaCall.CUBSLogonName = CUBSLogonName;
                currentAvayaCalls.put(avayaAgent.CurrentUCID, avayaCall);
            } catch (ResourceUnavailableException e) {
                resultCode = -1;
                resultText = "RESOURCE UNAVAILABLE (" + e.getMessage() + ") \n";
            } catch (InvalidStateException e) {
                resultCode = -1;
                resultText = "INVALID STATE (" + e.getMessage() + ") \n";
            } catch (PrivilegeViolationException e) {
                resultCode = -1;
                resultText = "PRIVILEGE VIOLATION (" + e.getMessage() + ") \n";
            } catch (MethodNotSupportedException e) {
                resultCode = -1;
                resultText = "METHOD NOT SUPPORTED (" + e.getMessage() + ") \n";
            } catch (TsapiInvalidPartyException e) {
                resultCode = -1;
                resultText = "INVALID PARTY.  LOGGED INTO YOUR PHONE? (" + e.getMessage() + ") \n";
            } catch (TsapiInvalidArgumentException e) {
                resultCode = -1;
                resultText = "INVALID ARGUMENT (" + e.getMessage() + ") \n";
            } catch (Error err) {
                //Send notification email
                StringWriter temp = new StringWriter();
                err.printStackTrace(new PrintWriter(temp));
                ErrorReportManager.reportErrorByEmail("AvayaLink Error", "Error in Dial.x"
                        + "PhoneNumberThread:  " + temp.toString());
            } finally {
                if (clientDialSocket != null) {
                    clientDialSocket.println(resultCode + SOCKET_FIELD_DELIMITER + resultText);
                    clientDialSocket.flush();
                    clientDialSocket.close();
                }
            }
        }
    }

    private class HangupPhoneNumberThread implements Runnable {

        private final AvayaAgent avayaAgent;
        private final PrintWriter clientHangupSocket;

        public HangupPhoneNumberThread(PrintWriter clientSocket, AvayaAgent avayaAgent) {
            this.clientHangupSocket = clientSocket;
            this.avayaAgent = avayaAgent;
        }

        @Override
        public void run() {
            int resultCode = 0;
            String resultText = "";
            String extensionNumber = avayaAgent.Extension;
            Terminal terminal = avayaAgent.JTAPITerminal;

            try {
                if (terminal.getTerminalConnections().length > 0) {
                    // hangup call, if any
                    disconnect(terminal.getTerminalConnections());
                                        
                    resultCode = 0;
                    resultText = "OK";
                }
            } catch (NullPointerException npe) {
                resultCode = -1;
                resultText = "NO ACTIVE CALL TO HANGUP PHONE FOR EXT# " + extensionNumber;
            } catch (Exception e) {
                resultCode = -1;
                resultText = "FAILED TO HANGUP PHONE FOR EXT# " + extensionNumber + " (" + e.getMessage() + ")\n";
            }

            if (clientHangupSocket != null) {
                clientHangupSocket.println(resultCode + SOCKET_FIELD_DELIMITER + resultText);
                clientHangupSocket.flush();
                clientHangupSocket.close();
            }
        }
    }
    
    private class WarmTransferThread implements Runnable {
        private final PrintWriter clientWarmTransferSocket;
        private final AvayaAgent avayaAgent;
        private final String CUBSLogonName;
        private final String transferNumber;
        private final String socketMessageReceived;
        int resultCode = 0;
        String resultText = "";

        public WarmTransferThread(PrintWriter clientSocket, AvayaAgent avayaAgent, String phoneNumber, String socketMessageReceived) {
            this.clientWarmTransferSocket = clientSocket;
            this.avayaAgent = avayaAgent;
            this.transferNumber = phoneNumber;
            this.CUBSLogonName = socketMessageReceived.split("~")[3];
            this.socketMessageReceived = socketMessageReceived;
        }
        
//        public void runNEW() {
//            Terminal terminal = avayaAgent.JTAPITerminal;
//            Address address = avayaAgent.JTAPIAddress;
//            String extensionNumber = avayaAgent.Extension;
//            Call transferController;
//            Call otherCall;
//            
//            otherCall = terminal.getAddresses()[0].getConnections()[0].getCall();
//            transferController = calls[(heldIndex + 1) % 2];
//            if (transferController instanceof CallControlCall) {
//                try {
//                    ((CallControlCall) transferController).transfer(otherCall);
//                } catch (Exception e) {
//                    
//                    //appendTrace(0, "exception caught " + e);
//                    MessageBox mb = new MessageBox(shell, SWT.OK | SWT.ICON_WARNING);
//                    mb.setMessage("Transfer failed!  " + e.getMessage());
//                    mb.open();
//                    return;
//                }
//            } else {
//                appendTrace(0, "transferController not instanceof CallControlCall");
//                MessageBox mb = new MessageBox(shell, SWT.OK | SWT.ICON_WARNING);
//                mb.setMessage("Transfer failed!  transferController not instanceof CallControlCall");
//                mb.open();
//                return;
//            }
//        }

        @Override
        public void run() {
            Terminal terminal = avayaAgent.JTAPITerminal;
            Address address = avayaAgent.JTAPIAddress;
            String extensionNumber = avayaAgent.Extension;

            try {
                // dial phone number
                LucentCallEx2 myCall = (LucentCallEx2) provider.createCall();
                UserToUserInfo uui = new UserToUserInfo("AVAYALINK:" + socketMessageReceived);               
                myCall.fastConnect(terminal, address, transferNumber, false, uui, "");

                LucentV5CallInfo lv5CallInfo = (LucentV5CallInfo) myCall;
                avayaAgent.CurrentUCID = lv5CallInfo.getUCID();

                resultCode = 0;
                resultText = "UCID:" + avayaAgent.CurrentUCID;
                
                AvayaCall avayaCall = new AvayaCall();
                avayaCall.CUBSLogonName = CUBSLogonName;
                currentAvayaCalls.put(avayaAgent.CurrentUCID, avayaCall);
            } catch (ResourceUnavailableException e) {
                resultCode = -1;
                resultText = "StationID:" + extensionNumber + ", ERROR: RESOURCE UNAVAILABLE (" + e.getMessage() + ") \n";
            } catch (InvalidStateException e) {
                resultCode = -1;
                resultText = "StationID:" + extensionNumber + ", ERROR: INVALID STATE (" + e.getMessage() + ") \n";
            } catch (PrivilegeViolationException e) {
                resultCode = -1;
                resultText = "StationID:" + extensionNumber + ", ERROR: PRIVILEGE VIOLATION (" + e.getMessage() + ") \n";
            } catch (MethodNotSupportedException e) {
                resultCode = -1;
                resultText = "StationID:" + extensionNumber + ", ERROR: METHOD NOT SUPPORTED (" + e.getMessage() + ") \n";
            } catch (TsapiInvalidPartyException e) {
                resultCode = -1;
                resultText = "StationID:" + extensionNumber + ", ERROR: INVALID PARTY (" + e.getMessage() + ") \n";
            } catch (TsapiInvalidArgumentException e) {
                resultCode = -1;
                resultText = "StationID:" + extensionNumber + ", ERROR: INVALID ARGUMENT (" + e.getMessage() + ") \n";
            } catch (Error err) {
                //Send notification email
                StringWriter temp = new StringWriter();
                err.printStackTrace(new PrintWriter(temp));
                ErrorReportManager.reportErrorByEmail("AvayaLink Error", "Error in Dial.x"
                        + "PhoneNumberThread:  " + temp.toString());
            } finally {
                if (clientWarmTransferSocket != null) {
                    clientWarmTransferSocket.println(resultCode + SOCKET_FIELD_DELIMITER + resultText);
                    clientWarmTransferSocket.flush();
                    clientWarmTransferSocket.close();
                }
            }
        }
    }    

    private void disconnect(TerminalConnection[] terminalConnections) {
        boolean found = false;
        Connection connection;

        if (terminalConnections != null) {
            if (terminalConnections.length == 1) {
                connection = terminalConnections[0].getConnection();

                if (connection != null) {
                    try {
                        disconnect(connection);
                    } catch (Exception e) {
                        eventLogWindow.append("\n\ndisconnect failure: " + e.getMessage() + "\n\n");
                    }
                }
            } else {
                for (TerminalConnection terminalConnection : terminalConnections) {
                    if (((CallControlTerminalConnection) terminalConnection).getCallControlState() == CallControlTerminalConnection.TALKING) {
                        found = true;
                        connection = terminalConnection.getConnection();
                        disconnect(connection);
                    }
                }
                if (!found) {
                    eventLogWindow.append("There are no Connections in the Talking state\n\n");
                }
            }
        }
    }

    private void disconnect(Connection connection) {
        int numberOfTries = 0;

        while (numberOfTries < 10) {
            if (connection != null) {
                try {
                    // IMPORTANT: This sleep seems to prevent the initial
                    // TsapiResourceUnavailableException error!
                    Thread.sleep(200);

                    connection.disconnect();
                    return;
                } catch (TsapiResourceUnavailableException truException) {
                    numberOfTries++;

                    try {
                        eventLogWindow.append("TsapiResourceUnavailableException exception #" + numberOfTries + "\n");
                        eventLogWindow.append("ErrorCode: " + truException.getErrorCode() + "\n");
                        eventLogWindow.append("ErrorType: " + truException.getErrorType() + "\n");

                        Thread.sleep(100);
                    } catch (Exception ee) {
                    }
                } catch (TsapiInvalidStateException iseException) {
                    return;
                } catch (TsapiPlatformException othException) {
                    return;
                } catch (Exception e) {
                    eventLogWindow.append("Connection.disconnect() caught " + e + "\n");
                    eventLogWindow.append("Message: " + e.getMessage() + "\n\n");

                    return;
                }
            }
        }
    }

    public void providerEventTransmissionEnded(ProviderEvent event) {
    }

    public void providerInService(ProviderEvent event) {
        handleProviderInService();
        AESServerOnline = true;
    }

    public void providerOutOfService(ProviderEvent event) {
        //TODO:comment
        try {
            ITsapiProvider iTsapiProvider;
            iTsapiProvider = (ITsapiProvider) event.getProvider();
            if (iTsapiProvider.getTsapiState() == ITsapiProvider.TSAPI_INITIALIZING) {
                return;
            }
        } catch (Exception e) {
        }

        AESServerOnline = false;

        if (configurationSetting.isTestMode()) {
            return;
        }

        eventLogWindow.appendCommand("Provider is now OUT OF SERVICE.\n", CommandType.SYSTEM, "");

        //Send notification 
        ErrorReportManager.reportErrorByEmail("AvayaLink Status: OUT OF SERVICE", "The AvayaLink software has lost connection to the AES server " + configurationSetting.getAESServiceName() + "\n");
    }

    public void providerShutdown(ProviderEvent event) {
        if (AESServerOnline) {
            AESServerOnline = false;
        }

        //TODO: reset everythinh
        extensionsBeingMonitored.clear();
        extensionsBeingMonitoredCount = 0;
        extensionsNotBeingMonitored.clear();
        extensionsNotBeingMonitoredCount = 0;
        UpdateList();

        if (configurationSetting.isTestMode()) {
            return;
        }

        //Send notification email
        ErrorReportManager.reportErrorByEmail("AvayaLink Status: SHUTDOWN", "The AvayaLink software is no longer connected to the AES server " + configurationSetting.getAESServiceName() + "\n");
    }

    private class SocketCommandProcessor implements SocketCommandListener {
        @Override
        public void onDialEvent(DialEvent event) {
            socketLogWindow.appendCommand("Received:" + event.getCommandLine() + "\n", CommandType.DIAL, event.getAgentExtension());

            AvayaAgent avayaAgent = (AvayaAgent) extensionsBeingMonitored.get(event.getAgentExtension());

            if (avayaAgent != null) {
                int numberCurrentConnections = 0;

                try {
                    //TODO: May want to check the status of each of the terminal connection(s)
                    numberCurrentConnections = avayaAgent.JTAPITerminal.getTerminalConnections().length;
                } catch (Exception e) {
                }

                //TODO: Bug?
                if (numberCurrentConnections > 0) {
                    event.getOutputSocketStream().println(-1 + SOCKET_FIELD_DELIMITER + "You already have an active call.");
                } else {
                    DialPhoneNumberThread dialPhoneNumberThread = new DialPhoneNumberThread(event.getOutputSocketStream(), avayaAgent, event.getPhoneNumber(), event.getCommandLine());

                    Thread dpnThread = new Thread(dialPhoneNumberThread);
                    if (IS_DEV_MODE) {
                        dpnThread.setName(event.getAgentExtension() + ":" + event.getPhoneNumber());
                    }
                    dpnThread.start();
                }
            } else {
                event.getOutputSocketStream().println(-1 + SOCKET_FIELD_DELIMITER + "No Avaya terminal found for x" + event.getAgentExtension());
            }
        }

        @Override
        public void onHangupEvent(HangupEvent event) {
            socketLogWindow.appendCommand("Received:" + event.getCommandLine() + "\n", CommandType.HANGUP, event.getAgentExtension());
            
            AvayaAgent avayaAgent = (AvayaAgent) extensionsBeingMonitored.get(event.getAgentExtension());

            if (avayaAgent != null) {
                HangupPhoneNumberThread hangupPhoneNumberThread = new HangupPhoneNumberThread(event.getOutputSocketStream(), avayaAgent);
                Thread hupThread = new Thread(hangupPhoneNumberThread);
                hupThread.start();
            } else {                
                event.getOutputSocketStream().println(-1 + SOCKET_FIELD_DELIMITER + "No Avaya terminal found for x" + event.getAgentExtension());
            }
        }
        
        @Override
        public void onWarmTransferEvent(WarmTransferEvent event) {
            socketLogWindow.appendCommand("Received:" + event.getCommandLine() + "\n", CommandType.WARMTRANSFER, event.getAgentExtension());

            AvayaAgent avayaAgent = (AvayaAgent) extensionsBeingMonitored.get(event.getAgentExtension());

            if (avayaAgent != null) {
                int numberCurrentConnections = 0;

                try {
                    //TODO: May want to check the status of each of the terminal connection(s)
                    numberCurrentConnections = avayaAgent.JTAPITerminal.getTerminalConnections().length;
                } catch (Exception e) {
                }

                //TODO: Bug?
                if (numberCurrentConnections < 1) {
                    event.getOutputSocketStream().println(-1 + SOCKET_FIELD_DELIMITER + "You do not have an active call to transfer.");
                } else {
                    WarmTransferThread warmTransferThread = new WarmTransferThread(event.getOutputSocketStream(), avayaAgent, event.getWarmTransferNumber(), event.getCommandLine());
                    Thread wtThread = new Thread(warmTransferThread);
                    wtThread.start();
                }
            } else {
                event.getOutputSocketStream().println(-1 + SOCKET_FIELD_DELIMITER + "No Avaya terminal found for x" + event.getAgentExtension());
            }            
        }

        @Override
        public void onGetStationInfoEvent(GetStationInfoEvent event) {
            socketLogWindow.appendCommand("Received:" + event.getCommandLine() + "\n", CommandType.SYSTEM, event.getAgentExtension());

            AvayaAgent avayaAgent = (AvayaAgent) extensionsBeingMonitored.get(event.getAgentExtension());

            if (avayaAgent != null) {
                String outputLine = "";

                outputLine = "STATION:" + avayaAgent.Extension + UNIT_SEPERATOR;
                outputLine = outputLine + "AGENTID:" + avayaAgent.AgentID + UNIT_SEPERATOR;
                outputLine = outputLine + "NAME:" + avayaAgent.Name + UNIT_SEPERATOR;
                outputLine = outputLine + "TYPE:" + avayaAgent.Type + UNIT_SEPERATOR;
                outputLine = outputLine + "PORT:" + avayaAgent.Port + UNIT_SEPERATOR;
                outputLine = outputLine + "MANUALDIAL:" + avayaAgent.AllowManualDialing.toString() + UNIT_SEPERATOR;
                outputLine = outputLine + "UCID:" + avayaAgent.CurrentUCID + UNIT_SEPERATOR;
                outputLine = outputLine + "PREVUCID:" + avayaAgent.LastUCIDChecked;

                event.getOutputSocketStream().println(0 + SOCKET_FIELD_DELIMITER + outputLine);
            } else {
                event.getOutputSocketStream().println(-1 + SOCKET_FIELD_DELIMITER + "No Avaya terminal found for x" + event.getAgentExtension());
            }
        }

        @Override
        public void onGetAgentIDEvent(GetAgentIdEvent event) {
            socketLogWindow.appendCommand("Received:" + event.getCommandLine() + "\n", CommandType.SYSTEM, event.getAgentExtension());

            int resultCode = 0;
            String outputLine;

            if (extensionsBeingMonitored.containsKey(event.getAgentExtension())) {
                AvayaAgent avayaAgent = extensionsBeingMonitored.get(event.getAgentExtension());
                if (! avayaAgent.AgentID.equals(""))
                    outputLine = avayaAgent.AgentID;               
                else
                    outputLine = avayaAgent.Extension;
            } else {
                resultCode = -1;
                outputLine = "ERROR: " + event.getAgentExtension() + " IS NOT BEING MONITORED BY AVAYALINK";
            }

            event.getOutputSocketStream().println(resultCode + SOCKET_FIELD_DELIMITER + outputLine);
        }

        @Override
        public void onGetAgentExtensionEvent(GetAgentExtensionEvent event) {
            socketLogWindow.appendCommand("Received:" + event.getCommandLine() + "\n", CommandType.SYSTEM, event.getAgentExtension());

            GetAgentExtensionThread getAgentExtensionThread = new GetAgentExtensionThread();
            getAgentExtensionThread.avayaAgentID = event.getAgentExtension();
            getAgentExtensionThread.clientSocket = event.getOutputSocketStream();
            Thread dpnThread = new Thread(getAgentExtensionThread);
            dpnThread.start();
        }

        @Override
        public void onUnknownSocketCommand(UnknownSocketCommandEvent event) {
            socketLogWindow.appendCommand("Received:" + event.getCommandLine() + "\n", CommandType.ERROR, event.getAgentExtension());
        }
    }

    @Action
    public Task EventLogResetDefault() {
        chkShowRegistrations.setSelected(false);
        chkShowDeregistrations.setSelected(true);
        chkShowConnects.setSelected(true);
        chkShowFailures.setSelected(true);
        chkShowDisconnects.setSelected(true);
        chkShowDNDs.setSelected(true);
        chkShowWarnings.setSelected(true);

        chkEventFilterExtensions.setSelected(false);

        SetEventLogFilters();

        return new EventLogResetDefaultTask(getApplication());
    }

    private class EventLogResetDefaultTask extends org.jdesktop.application.Task<Object, Void> {

        EventLogResetDefaultTask(org.jdesktop.application.Application app) {
            // Runs on the EDT.  Copy GUI state that
            // doInBackground() depends on from parameters
            // to EventLogResetDefaultTask fields, here.
            super(app);
        }

        @Override
        protected Object doInBackground() {
            // Your Task's code here.  This method runs
            // on a background thread, so don't reference
            // the Swing GUI from here.
            return null;  // return your result
        }

        @Override
        protected void succeeded(Object result) {
            // Runs on the EDT.  Update the GUI based on
            // the result computed by doInBackground().
        }
    }

    @Action
    public Task SocketLogResetDefault() {
        chkShowDials.setSelected(true);
        chkShowHangups.setSelected(true);

        chkSocketFilterExtensions.setSelected(false);

        SetSocketLogFilters();

        return new SocketLogResetDefaultTask(getApplication());
    }

    private class SocketLogResetDefaultTask extends org.jdesktop.application.Task<Object, Void> {

        SocketLogResetDefaultTask(org.jdesktop.application.Application app) {
            // Runs on the EDT.  Copy GUI state that
            // doInBackground() depends on from parameters
            // to SocketLogResetDefaultTask fields, here.
            super(app);
        }

        @Override
        protected Object doInBackground() {
            // Your Task's code here.  This method runs
            // on a background thread, so don't reference
            // the Swing GUI from here.
            return null;  // return your result
        }

        @Override
        protected void succeeded(Object result) {
            // Runs on the EDT.  Update the GUI based on
            // the result computed by doInBackground().
        }
    }

    @Action
    public final void SetEventLogFilters() {
        if (chkShowRegistrations.isSelected()) {
            eventLogWindow.EventFilterRegisters = false;
        } else {
            eventLogWindow.EventFilterRegisters = true;
        }

        eventLogWindow.EventFilterDeregisters = !chkShowDeregistrations.isSelected();
        eventLogWindow.EventFilterConnects = !chkShowConnects.isSelected();
        eventLogWindow.EventFilterDisconnects = !chkShowDisconnects.isSelected();
        eventLogWindow.EventFilterWarnings = !chkShowWarnings.isSelected();
        eventLogWindow.EventFilterFailures = !chkShowFailures.isSelected();
        eventLogWindow.EventFilterDNDs = !chkShowDNDs.isSelected();

        if (chkEventFilterExtensions.isSelected()) {
            eventLogWindow.EventFilterExtensions = true;
            eventLogWindow.SelectedExtensions = lstExtensionsBeingMonitored.getSelectedValues();
        } else {
            eventLogWindow.EventFilterExtensions = false;
            eventLogWindow.SelectedExtensions = null;
        }
    }

    @Action
    public final void SetSocketLogFilters() {
        socketLogWindow.SocketFilterDials = !chkShowDials.isSelected();
        socketLogWindow.SocketFilterHangups = !chkShowHangups.isSelected();

        if (chkSocketFilterExtensions.isSelected()) {
            socketLogWindow.SocketFilterExtensions = false;
            socketLogWindow.SelectedExtensions = null;
        } else {
            socketLogWindow.SocketFilterExtensions = true;
            socketLogWindow.SelectedExtensions = lstExtensionsBeingMonitored.getSelectedValues();
        }
    }

    @Action
    public void ViewStationData() {
        if (lstExtensionsBeingMonitored.getSelectedValues().length != 1) 
            return;

        try {
            AvayaAgent avayaAgent = (AvayaAgent) extensionsBeingMonitored.get(lstExtensionsBeingMonitored.getSelectedValue().toString());
            JFrame mainFrame = AvayaLinkApp.getApplication().getMainFrame();
            AvayaLinkViewStation viewStation = new AvayaLinkViewStation(mainFrame, false, avayaAgent);
            AvayaLinkApp.getApplication().show(viewStation);
        } catch (Exception e) {
            ErrorReportManager.reportErrorByEmail("AvayaLink ERROR", "There was an exception in the ViewStationData routine.  (" + e.getMessage() + ")");
        }
    }

    @Action
    public boolean QuitApplication() {
        Boolean OkToQuit;

        int response = JOptionPane.showConfirmDialog(null,
                "Are you sure you want to quit?",
                "AvayaLink Exit Confirmation",
                JOptionPane.YES_NO_OPTION,
                JOptionPane.QUESTION_MESSAGE);

        if (response == JOptionPane.YES_OPTION) {
            try {
                provider.shutdown();
            } catch (Exception e) {}
           
            OkToQuit = true;
        } else {
            OkToQuit = false;
        }

        return OkToQuit;
    }
    // Variables declaration - do not modify//GEN-BEGIN:variables
    public javax.swing.JButton btnEventResetDefault;
    public javax.swing.JButton btnSocketResetDefault;
    private javax.swing.JCheckBox chkAllowManualDialing;
    public javax.swing.JCheckBox chkEventFilterExtensions;
    private javax.swing.JCheckBox chkShowConnects;
    private javax.swing.JCheckBox chkShowDNDs;
    private javax.swing.JCheckBox chkShowDeregistrations;
    private javax.swing.JCheckBox chkShowDials;
    private javax.swing.JCheckBox chkShowDisconnects;
    private javax.swing.JCheckBox chkShowFailures;
    private javax.swing.JCheckBox chkShowHangups;
    private javax.swing.JCheckBox chkShowRegistrations;
    private javax.swing.JCheckBox chkShowTransfers;
    private javax.swing.JCheckBox chkShowWarnings;
    public javax.swing.JCheckBox chkSocketFilterExtensions;
    public javax.swing.JButton cmdExitApplication;
    public javax.swing.JButton cmdStartMonitor;
    public javax.swing.JMenu fileView;
    public javax.swing.JPanel jPanel1;
    public javax.swing.JPanel jPanel2;
    private javax.swing.JPanel jPanel3;
    public javax.swing.JScrollPane jScrollPane1;
    public javax.swing.JLabel lblExtensionsBeingMonitored;
    public javax.swing.JLabel lblHeartbeatText;
    public javax.swing.JList lstExtensionsBeingMonitored;
    public javax.swing.JPanel mainPanel;
    public javax.swing.JMenuBar menuBar;
    public javax.swing.JPopupMenu popExtensionsBeingMonitored;
    public javax.swing.JMenuItem popViewAvayaStation;
    private javax.swing.JProgressBar progressBar;
    public javax.swing.JSplitPane sppSplitter;
    private javax.swing.JLabel statusAnimationLabel;
    private javax.swing.JLabel statusMessageLabel;
    public javax.swing.JPanel statusPanel;
    public mytextarea.MyTextArea txtCommandLog;
    public mytextarea.MyTextArea txtSessionLog;
    public javax.swing.JMenuItem viewStationMenuItem;
    // End of variables declaration//GEN-END:variables
    private final Timer messageTimer;
    private final Timer busyIconTimer;
    private final Icon idleIcon;
    private final Icon[] busyIcons = new Icon[15];
    private int busyIconIndex = 0;
    private JDialog aboutBox;
}
