# Rotomina

A comprehensive web-based management and monitoring tool for Android devices with MITM and PlayIntegrityFix support, designed for Pokemon GO automation and management.

![Rotomina Dashboard](screenshots/dashboard.png)

## 🏗️ Architecture

Rotomina is built with a modern, scalable architecture:

- **Backend**: FastAPI with async/await support for high-performance concurrent operations
- **Frontend**: Alpine.js for reactive UI with Tailwind CSS for responsive design
- **Real-time Communication**: WebSocket connections for live device status updates
- **Connection Management**: Optimized ADB connection pooling and WebSocket connection reuse
- **Background Tasks**: Scheduled tasks for updates, monitoring, and maintenance
- **Authentication**: Session-based user authentication with secure credentials

## 🚀 Features

- 📱 **Device Management**: Monitor and control multiple Android devices via ADB
- 🔄 **Automatic Updates**: Keep Pokemon GO, MITM apps, and PlayIntegrityFix up-to-date
- � **Real-time Monitoring**: WebSocket-based live status updates with fallback AJAX polling
- � **Discord Notifications**: Configurable alerts for device status and updates
- 🛠️ **Remote Management**: Install apps, modules, and restart services remotely
- 🔐 **Secure Authentication**: User authentication with configurable credentials
- 🌐 **Responsive Design**: Mobile-friendly interface that works on all devices
- 🔧 **Connection Optimization**: Efficient connection pooling to minimize resource usage

## 📋 Requirements

### System Requirements
- Python 3.8+
- ADB (Android Debug Bridge) installed and accessible
- Network access to Android devices

### Device Requirements
- Root access on Android devices
- Magisk installed
- PlayIntegrityFix module
- MITM apps compatible with Pokemon GO
- Network connectivity (WiFi or USB connection)

## 🛠️ Installation

### Quick Start (Using Docker Compose) - Recommended

The easiest way to run Rotomina is using Docker Compose with pre-built image:

1. **Download the standalone configuration:**
```bash
curl -O https://raw.githubusercontent.com/f3ger/rotomina/main/standalone-docker-compose.yml
mv standalone-docker-compose.yml docker-compose.yml
```

2. **Create necessary directories:**
```bash
mkdir -p data
```

3. **Start Rotomina:**
```bash
docker-compose up -d
```

**Default credentials will be created automatically:**
- Username: `admin`
- Password: `admin`

> ⚠️ **SECURITY WARNING**: Change these credentials immediately after first login!

4. **Access the web interface** at http://localhost:8000

### Alternative Installation Methods

#### Docker Run Command
```bash
docker run -d \
  --name rotomina \
  --restart unless-stopped \
  -p 8000:8000 \
  -v $(pwd)/config.json:/app/config.json \
  -v $(pwd)/data:/app/data \
  --privileged \
  ghcr.io/f3ger/rotomina:latest
```

#### Building from Source
```bash
# Clone the repository
git clone https://github.com/f3ger/rotomina.git
cd rotomina

# Build and run with Docker Compose
docker-compose build
docker-compose up -d
```

#### Manual Installation (Advanced)
```bash
# Clone repository
git clone https://github.com/f3ger/rotomina.git
cd rotomina

# Create virtual environment
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# Install dependencies
pip install -r requirements.txt

# Start the server
uvicorn main:app --host 0.0.0.0 --port 8000
```

## ⚙️ Configuration

### Initial Setup
On first run, a `config.json` file will be created with default settings:

```json
{
  "users": [
    {
      "username": "admin",
      "password": "admin"
    }
  ],
  "devices": [
    {
      "ip": "1.2.3.4:5555",
      "display_name": "demo",
      "control_enabled": true,
      "memory_threshold": 200,
      "memory_unit": "MB"
    }
  ],
  "rotomApiUrl": "http://rotom.example.com/api/status",
  "rotomApiUser": "user_name", 
  "rotomApiPass": "password",
  "discord_webhook_url": "https://discord.com/api/webhooks/1234567890/abcdefg",
  "api_check_interval": 60,
  "memory_threshold": 100,
  "pif_auto_update_enabled": false,
  "pogo_auto_update_enabled": true,
  "preferred_module_type": "fix",
  "device_token": "device_token"
}
```

### Device Management
Add devices via the web interface using:
- **IP Address**: For network-connected devices (format: `IP:PORT`, e.g., `192.168.1.100:5555`)
- **ADB Device ID**: For USB-connected devices (format: `DEVICE_ID`, e.g., `11131FDD4001BU`)

### Configuration Options
- `memory_threshold`: Memory limit in MB before automatic restart
- `pogo_auto_update_enabled`: Auto-update Pokemon GO when new versions available
- `pif_auto_update_enabled`: Auto-update PlayIntegrityFix module
- `discord_webhook_url`: Discord webhook for notifications
- `device_token`: Authentication token for external API access

## 🎯 Usage

### Getting Started
1. **Access the web interface** at `http://your-server-ip:8000`
2. **Log in** with your configured credentials
3. **Add devices** in the Settings page
4. **Monitor and manage** devices from the Status page

### Status Page Features
The Status page provides comprehensive device information:
- **Connection Status**: Online/Offline with real-time updates
- **Memory Usage**: Current memory consumption with visual indicators
- **Installed Versions**: Pokemon GO, MITM, and module versions
- **Update Controls**: Manual update triggers for each component
- **Runtime Tracking**: How long devices have been running
- **Device Controls**: Restart, update, and manage individual devices

### WebSocket Communication
- **Primary Connection**: WebSocket for real-time updates (`ws://host:8000/ws/status`)
- **Fallback Mechanism**: AJAX polling every 60 seconds if WebSocket fails
- **Connection Pooling**: Optimized connection reuse to minimize overhead
- **Automatic Reconnection**: Handles connection drops gracefully

### API Endpoints
- `GET /api/status`: Device status and system information
- `GET /api/all-module-versions`: Available module versions
- `POST /devices/add`: Add new device
- `POST /devices/remove`: Remove device
- `WebSocket /ws/status`: Real-time status updates

## 🔔 Discord Notifications

Configure Discord notifications by adding a webhook URL in Settings to receive alerts for:
- Device offline/online status changes
- Memory threshold breaches and automatic restarts
- Update completion and failures
- Installation progress and results
- System errors and warnings

### Notification Types
- **INFO**: General status updates
- **WARNING**: Memory thresholds, connection issues
- **ERROR**: Failed updates, critical system errors

## 🔄 Updating

### Docker Updates
```bash
# Pull latest image and restart
docker-compose pull
docker-compose up -d
```

### Source Updates
```bash
# Pull latest changes
git pull origin main

# Rebuild and restart
docker-compose build
docker-compose up -d
```

## 🐛 Troubleshooting

### Common Issues

#### WebSocket Connection Issues
- **Symptom**: Frequent API polling instead of WebSocket updates
- **Solution**: Check firewall settings, ensure port 8000 is accessible
- **Fallback**: System automatically uses AJAX polling if WebSocket fails

#### Device Connection Problems
- **Symptom**: Devices showing as offline
- **Solution**: 
  - Verify ADB is installed and accessible
  - Check network connectivity to device IP
  - Ensure device has USB debugging enabled
  - Confirm device is rooted with Magisk

#### Memory Issues
- **Symptom**: Frequent device restarts
- **Solution**: 
  - Increase `memory_threshold` in config
  - Check for memory leaks in installed apps
  - Monitor device performance logs

#### Update Failures
- **Symptom**: Updates not installing
- **Solution**:
  - Check internet connectivity
  - Verify sufficient storage space
  - Ensure device has proper permissions
  - Review update logs for specific error messages

### Performance Optimization
- **Connection Pooling**: Automatically manages ADB connections efficiently
- **WebSocket Optimization**: Reuses connections to minimize overhead
- **Background Tasks**: Scheduled operations to prevent blocking
- **Memory Management**: Monitors and cleans up stale connections

## 🔒 Security Considerations

- **Default Credentials**: Always change from `admin:admin`
- **Network Access**: Restrict access to trusted networks
- **API Tokens**: Keep device tokens secure and rotate regularly
- **HTTPS**: Use SSL/TLS in production environments
- **Firewall**: Configure appropriate firewall rules

## 🏗️ Development

### Project Structure
```
rotomina/
├── main.py              # Main FastAPI application
├── templates/           # HTML templates
│   ├── base.html       # Base template with navigation
│   ├── status.html     # Device status dashboard
│   ├── settings.html   # Configuration management
│   └── login.html      # Authentication page
├── static/             # Static assets (CSS, JS, images)
├── data/               # Application data directory
└── config.json         # Configuration file
```

### Key Components
- **ConnectionManager**: WebSocket connection pooling and management
- **ADBConnectionPool**: Optimized ADB device connections
- **VersionManager**: Component version tracking and updates
- **DeviceMonitor**: Background device status monitoring
- **UpdateManager**: Automated update orchestration

## 📝 License

This project is licensed under the MIT License - see the LICENSE file for details.

## 🙏 Acknowledgements

- The Pokemon GO community for tools and research
- MITM developers for interception capabilities
- PlayIntegrityFix module developers
- FastAPI framework contributors
- Alpine.js and Tailwind CSS teams

## ⚠️ Disclaimer

This project is not affiliated with Niantic or The Pokémon Company. Use at your own risk and responsibility. Ensure compliance with Pokemon GO Terms of Service and local laws.

## 📞 Support

For issues, feature requests, or contributions:
- **GitHub Issues**: [Create an issue](https://github.com/f3ger/rotomina/issues)
- **Documentation**: Check this README and inline code comments
- **Community**: Join the community discussions
