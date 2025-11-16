# Lean4 Development Environments

This directory contains two Podman-based environments for working with Lean4:

1. **`lean4/`** - Complete development environment with PDF generation capabilities
2. **`jupyter/`** - Interactive Jupyter notebook environment for Lean4

## Quick Start

### PDF Generation Environment

```powershell
cd environments/lean4
podman-compose up -d
podman exec -it lean4-container bash
```

### Jupyter Environment

```powershell
cd environments/jupyter
podman-compose up -d
# Open browser to http://localhost:8888
```

## Environment Details

### Lean4 + PDF Generation (`lean4/`)

**Purpose**: Full-featured Lean4 development with LaTeX/PDF output capabilities

**Features**:
- Lean4 v4.12.0 with Mathlib
- LaTeX/TeXLive for document generation
- Python environment for PDF processing
- Custom proof-to-PDF conversion tools
- Sample mathematical proofs

**Key Files**:
- `Dockerfile` - Container definition with Lean4 + LaTeX
- `docker-compose.yml` - Service configuration
- `scripts/generate-pdf.sh` - Linux PDF generation script
- `scripts/generate-pdf.cmd` - Windows PDF generation script
- `scripts/simple_lean_parser.py` - Lean code to LaTeX converter

**Usage**:
```bash
# Inside container
cd /workspace
./scripts/generate-pdf.sh /workspace/examples/math_proofs/MathProofs.lean
# Output: /workspace/output/MathProofs.pdf
```

### Lean4 + Jupyter (`jupyter/`)

**Purpose**: Interactive notebook-based Lean4 development and learning

**Features**:
- Jupyter Lab with Lean4 kernel integration
- Custom Lean4 kernel for code execution
- Pre-built tutorial notebooks
- Web-based interactive development
- Real-time proof checking

**Key Files**:
- `Dockerfile` - Container with Jupyter + Lean4
- `docker-compose.yml` - Service configuration with port mapping
- `kernel/lean4_kernel.py` - Custom Jupyter kernel for Lean4
- `kernel/kernel.json` - Kernel specification
- `notebooks/Lean4_Tutorial.ipynb` - Comprehensive tutorial

**Usage**:
```bash
# Start the service
podman-compose up -d

# Access Jupyter Lab
# Open browser to: http://localhost:8888
```

## Prerequisites

- **Podman**: Container runtime
- **Podman Compose**: For orchestration
- **Windows PowerShell** (for Windows scripts)

### Installation (Windows)

```powershell
# Install Podman Desktop
winget install RedHat.Podman-Desktop

# Or install Podman CLI only
winget install RedHat.Podman

# Install podman-compose
pip install podman-compose
```

## Container Architecture

### Base Images
- **Lean4 Environment**: `ubuntu:22.04` + Lean4 toolchain
- **Jupyter Environment**: `ubuntu:22.04` + Lean4 + Python + Jupyter

### Volume Mounts
- `../examples:/workspace/examples` - Shared example code
- `./output:/workspace/output` - Generated files
- `./notebooks:/workspace/notebooks` - Jupyter notebooks (Jupyter env only)

### Network Configuration
- **Lean4**: No exposed ports (development container)
- **Jupyter**: Port 8888 mapped to host

## Example Workflows

### 1. Creating Mathematical Proofs with PDF Output

```bash
# 1. Start the lean4 environment
cd environments/lean4
podman-compose up -d

# 2. Create your Lean4 file
# Edit examples/my_proof.lean

# 3. Generate PDF
podman exec -it lean4-container bash
cd /workspace
./scripts/generate-pdf.sh examples/my_proof.lean

# 4. View generated PDF
# Check output/my_proof.pdf
```

### 2. Interactive Development with Jupyter

```bash
# 1. Start Jupyter environment
cd environments/jupyter
podman-compose up -d

# 2. Open browser
# Navigate to http://localhost:8888

# 3. Create new notebook or open tutorial
# Work with Lean4 code in interactive cells

# 4. Execute Lean4 code in cells
# Real-time feedback and type checking
```

## Troubleshooting

### Common Issues

**Podman not found**:
```powershell
# Install Podman Desktop or CLI
winget install RedHat.Podman-Desktop
```

**Port 8888 already in use** (Jupyter):
```yaml
# Edit docker-compose.yml in jupyter/
ports:
  - "8889:8888"  # Use different port
```

**Container won't start**:
```bash
# Check logs
podman-compose logs

# Rebuild container
podman-compose down
podman-compose up --build
```

**PDF generation fails**:
```bash
# Check LaTeX installation in container
podman exec -it lean4-container which pdflatex

# Check Python dependencies
podman exec -it lean4-container python3 -c "import sys; print(sys.path)"
```

### File Permissions (Linux/WSL)

```bash
# Ensure proper permissions
chmod +x environments/lean4/scripts/generate-pdf.sh
chmod +x environments/jupyter/scripts/setup-kernel.sh
```

## Directory Structure

```
environments/
├── README.md                    # This file
├── lean4/                       # PDF Generation Environment
│   ├── Dockerfile
│   ├── docker-compose.yml
│   ├── scripts/
│   │   ├── generate-pdf.sh
│   │   ├── generate-pdf.cmd
│   │   └── simple_lean_parser.py
│   └── output/                  # Generated PDFs
└── jupyter/                     # Jupyter Environment
    ├── Dockerfile
    ├── docker-compose.yml
    ├── kernel/
    │   ├── lean4_kernel.py
    │   └── kernel.json
    ├── notebooks/
    │   └── Lean4_Tutorial.ipynb
    └── scripts/
        └── setup-kernel.sh
```

## Advanced Configuration

### Customizing Lean4 Version

Edit the Dockerfile in either environment:

```dockerfile
# Change Lean4 version
ENV LEAN_VERSION="v4.11.0"  # or desired version
```

### Adding Additional Python Packages

For the Jupyter environment:

```dockerfile
# In Dockerfile, add to the pip install command
RUN pip3 install jupyter jupyterlab ipython notebook \
                 your-additional-package
```

### Custom LaTeX Packages

For the PDF generation environment:

```dockerfile
# Add to Dockerfile
RUN apt-get update && apt-get install -y \
    texlive-latex-extra \
    texlive-fonts-extra \
    your-latex-package
```

## Contributing

When adding new features:

1. Test in both environments if applicable
2. Update this README with new functionality
3. Add example usage in the examples/ directory
4. Ensure cross-platform compatibility (Windows/Linux)

## Resources

- [Lean4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Podman Documentation](https://docs.podman.io/)
- [Jupyter Documentation](https://jupyter.org/documentation)

## License

These environment configurations are provided as-is for educational and development purposes.