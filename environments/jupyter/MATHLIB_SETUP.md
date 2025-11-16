# Adding Mathlib to Lean4 Jupyter Environment

This guide explains how to add Mathlib (Lean's mathematical library) to your Jupyter environment.

## Current Status

The Jupyter environment currently includes:
- ✅ Lean4 v4.11.0 core libraries
- ✅ Basic mathematical operations (Nat, List, etc.)
- ✅ Core proof tactics
- ❌ Mathlib (advanced mathematical library)

## Why Add Mathlib?

Mathlib provides:
- Advanced mathematical structures (Real numbers, Groups, Rings, etc.)
- Thousands of mathematical theorems
- Sophisticated proof automation
- Integration with modern mathematics

## Option 1: Modify Dockerfile (Recommended)

Add to the Dockerfile after the Lean4 installation:

```dockerfile
# Install Mathlib
USER root
RUN mkdir -p /opt/mathlib
WORKDIR /opt/mathlib

# Clone Mathlib
RUN git clone https://github.com/leanprover-community/mathlib4.git . && \
    git checkout v4.11.0

# Build Mathlib (this takes a long time!)
USER $USERNAME
RUN cd /opt/mathlib && lake build

# Set environment for Mathlib
ENV LEAN_PATH="/opt/mathlib/lib:$LEAN_PATH"
```

## Option 2: Lake Project Setup

Create a `lakefile.lean` in your project:

```lean
import Lake
open Lake DSL

package «lean4-jupyter» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.11.0"

@[default_target]
lean_lib «Lean4Jupyter» {
  -- add any library configuration options here
}
```

Then run:
```bash
lake update
lake build
```

## Option 3: Container Runtime Setup

Install Mathlib at runtime:

```bash
# Inside the container
podman exec -it lean4-jupyter-container bash

# Navigate to workspace
cd /workspace

# Initialize lake project
lake init mathlib-project
cd mathlib-project

# Add mathlib dependency
echo 'require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"v4.11.0"' >> lakefile.lean

# Update and build
lake update
lake build
```

## Testing Mathlib Installation

Create a new notebook cell:

```lean4
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs

-- Test real numbers
example (x y : ℝ) : x + y = y + x := by
  rw [add_comm]

-- Test that it works
#check Real
#check Group
```

## Performance Considerations

⚠️ **Warning**: Building Mathlib takes significant time and resources:
- **Build time**: 30+ minutes on most systems
- **Disk space**: ~2GB additional storage
- **Memory**: 4GB+ RAM recommended during build

## Recommended Approach

For learning Lean4:
1. Start with core libraries (current setup)
2. Learn basic proof techniques
3. Add Mathlib when you need advanced mathematics

For research/advanced use:
1. Modify Dockerfile to include Mathlib
2. Build once, use many times
3. Consider using pre-built Mathlib images

## Pre-built Alternative

Consider using a pre-built image with Mathlib:

```dockerfile
FROM leanprover/lean4:v4.11.0-mathlib
# Your customizations here
```

## Troubleshooting

**Build fails**: Ensure sufficient memory and disk space
**Import errors**: Check LEAN_PATH environment variable
**Slow performance**: Mathlib builds are CPU-intensive

## Next Steps

Once Mathlib is installed, you can:
- Import advanced mathematical structures
- Use sophisticated automation tactics
- Access thousands of pre-proven theorems
- Work with real analysis, algebra, topology, etc.

## Resources

- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Mathlib Installation Guide](https://leanprover-community.github.io/install/project.html)