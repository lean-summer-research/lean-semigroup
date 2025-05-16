# Project Structure

## Files and Organization

### Main Project Files (`MyProject` folder)
- **PnatPow.lean**: Defines exponentiation for semigroups using positive natural numbers
- **WithOne.lean**: Implements the `S¹` construction for turning semigroups into monoids
- **Idempotence.lean**: Proves theorems about idempotent elements in finite semigroups
- **GreensRelations.lean**: Formalizes Green's relations (R, L, J, H) for classifying elements

### Examples (`Examples` folder)
- **Threemap.lean**: Defines the monoid of functions on {0,1,2} under composition and characterizes Greens relations on it.
- **WithOneExample.lean**: Demonstrates how to apply monoid theorems to semigroups using definitions from `WithOne.lean`
- **HSversionApr21.lean**: Unchanged

## Import Structure
```
Mathlib
  ↓
PnatPow.lean
  ↓
WithOne.lean
  ↓
Idempotence.lean
  ↓
GreensRelations.lean
  ↙          ↘
Threemap.lean  WithOneExample.lean
```

# Using Github Codespaces

There are two ways to use this repository:

1. Clone the repository and use it normally, ignoring the `.devcontainer` folder.
2. (also easy) Use GitHub Codespaces, which gives you a pre-configured development environment in your browser (explained below).

When you open this repo in a codespace, you'll see a VS Code interface in your browser. It's automatically set up with the LEAN4 vscode extention, correct lean version, and mathlib cache. It all runs on github's infra, so you don't have to worry about any of your local Lean, Elan, or VScode installations.

## First Time Setup:
1. Click the green "<> Code" button at the top of this GitHub page
2. Select "Codespaces" tab
3. Click "Create codespace"
4. Wait about 5-10 minutes for initial setup

## Basic Git Commands:
  First you have to open the integrated terminal (Mac: `Cmd+(backtick)`, Windows: `Ctrl+(backtick)`)

```bash
# Download latest changes
git pull

# Save your changes
# Stage all changes in the current working directory (make sure you are in the directory you want to save)
git add .

# Save changes locally
git commit -m "example"

# Upload changes to GitHub
git push
```

## Returning Later:
Go back to the repository's "<> Code" button, select "Codespaces" tab, and click your existing codespace (starts a lot faster than the initial build).

## How It Works (and how to do it locally)

The `.devcontainer` folder contains configuration files for a "dev container," which is like a small virtual machine. It sets up everything needed, like the operating system and software such as VSCode and Lean. GitHub Codespaces uses these files to create a development environment in the cloud, using Docker to manage the setup.

Docker is a tool that runs dev containers on your local computer. If you prefer not to use GitHub's cloud, you can run the same dev container locally instead of using Codespaces:

1. Install Docker Desktop from docker.com
2. In VS Code, install the "Dev Containers" extension
3. Clone this repository
4. Open the folder in VS Code
5. Click "Reopen in Container" when prompted

This will give you the same environment as Codespaces but running on your local machine. The VScode extension should automatically reopen the same container when you reopen the folder so you only have to build the container once.
