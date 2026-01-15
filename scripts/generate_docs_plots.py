import numpy as np
import matplotlib.pyplot as plt
import os

def ensure_dir():
    if not os.path.exists('../docs/images'):
        os.makedirs('../docs/images')

def green_function(c, z, max_iter=100, R=2.0):
    g = np.zeros_like(z, dtype=float)
    escaped = np.zeros_like(z, dtype=bool)
    zn = z.copy()
    escape_radius = max(R, abs(c) + 0.1) if abs(c) > 0 else 2.0
    if abs(c) > 2: escape_radius = abs(c)
    
    for n in range(max_iter):
        mask = (~escaped) & (np.abs(zn) > escape_radius)
        if np.any(mask):
            g[mask] = (1.0 / (2**n)) * np.log(np.abs(zn[mask]))
            escaped[mask] = True
        not_escaped = ~escaped
        zn[not_escaped] = zn[not_escaped]**2 + c
    return g

def plot_annulus():
    print("Generating puzzle_annulus.png...")
    c = -1
    extent = [-0.8, 0.8, -0.8, 0.8]
    x = np.linspace(extent[0], extent[1], 400)
    y = np.linspace(extent[2], extent[3], 400)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    G = green_function(c, Z)
    
    fig, ax = plt.subplots(figsize=(6, 6))
    ax.imshow(G, extent=extent, origin='lower', cmap='bone_r', vmax=1.0, alpha=0.3)
    # Highlight A_1 (between 0.25 and 0.5)
    ax.contourf(X, Y, G, levels=[0.25, 0.5], colors=['#ffcc00'], alpha=0.6)
    
    levels = [0.125, 0.25, 0.5]
    colors = ['green', 'red', 'blue']
    cs = ax.contour(X, Y, G, levels=levels, colors=colors, linewidths=1.5)
    ax.clabel(cs, fmt='%.3f')
    ax.plot(0, 0, 'ro', label='0')
    ax.set_title(r"Puzzle Annulus $A_1 = P_1(0) \setminus P_2(0)$")
    ax.legend()
    plt.tight_layout()
    plt.savefig('../docs/images/puzzle_annulus.png', dpi=150)
    plt.close()

def plot_para_puzzle():
    print("Generating para_puzzle.png...")
    extent = [-2.0, 1.0, -1.2, 1.2]
    x = np.linspace(extent[0], extent[1], 400)
    y = np.linspace(extent[2], extent[3], 320)
    X, Y = np.meshgrid(x, y)
    C = X + 1j * Y
    
    g_param = np.zeros_like(C, dtype=float)
    escaped = np.zeros_like(C, dtype=bool)
    Zn = np.zeros_like(C, dtype=complex) # Start at critical point 0
    
    for n in range(50):
        mask = (~escaped) & (np.abs(Zn) > 4.0)
        if np.any(mask):
            g_param[mask] = (1.0 / (2**n)) * np.log(np.abs(Zn[mask]))
            escaped[mask] = True
        not_escaped = ~escaped
        Zn[not_escaped] = Zn[not_escaped]**2 + C[not_escaped]
        
    fig, ax = plt.subplots(figsize=(8, 6))
    ax.imshow(g_param, extent=extent, origin='lower', cmap='bone_r', vmax=1.0)
    ax.contourf(X, Y, g_param, levels=[0, 0.001], colors=['black'])
    levels = [0.125, 0.25, 0.5, 1.0]
    colors = ['orange', 'green', 'blue', 'purple']
    cs = ax.contour(X, Y, g_param, levels=levels, colors=colors)
    ax.clabel(cs, fmt='%.3f')
    ax.set_title(r"Para-Puzzle Pieces $\mathcal{P}_n$")
    plt.tight_layout()
    plt.savefig('../docs/images/para_puzzle.png', dpi=150)
    plt.close()

def plot_nesting():
    print("Generating puzzle_nesting.png...")
    c = -1
    extent = [-0.8, 0.8, -0.8, 0.8]
    x = np.linspace(extent[0], extent[1], 300)
    y = np.linspace(extent[2], extent[3], 300)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    G = green_function(c, Z)
    
    fig, ax = plt.subplots(figsize=(6, 6))
    levels = [0.0625, 0.125, 0.25, 0.5]
    colors = ['red', 'orange', 'green', 'blue']
    cs = ax.contour(X, Y, G, levels=levels, colors=colors, linewidths=2)
    ax.text(0, 0, '$0$', color='black', ha='center', va='center', fontweight='bold')
    ax.set_title(r"Nesting: $P_{n+1}(0) \subset P_n(0)$")
    plt.tight_layout()
    plt.savefig('../docs/images/puzzle_nesting.png', dpi=150)
    plt.close()

def plot_persistence():
    print("Generating puzzle_persistence.png...")
    c = -0.123 + 0.745j
    extent = [-1.5, 1.5, -1.5, 1.5]
    x = np.linspace(extent[0], extent[1], 300)
    y = np.linspace(extent[2], extent[3], 300)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    G = green_function(c, Z)
    
    fig, ax = plt.subplots(figsize=(6, 6))
    ax.contourf(X, Y, G, levels=[0, 0.005], colors=['black'])
    levels = [0.01, 0.05, 0.1]
    ax.contour(X, Y, G, levels=levels, cmap='autumn')
    ax.plot(0, 0, 'wo', markeredgecolor='red', label='Critical Point 0')
    ax.set_title(r"Persistence ($c \in \mathcal{M}$)")
    ax.legend()
    plt.tight_layout()
    plt.savefig('../docs/images/puzzle_persistence.png', dpi=150)
    plt.close()

def plot_empty():
    print("Generating puzzle_empty.png...")
    c = -2.1
    extent = [-2.5, 2.5, -1.5, 1.5]
    x = np.linspace(extent[0], extent[1], 300)
    y = np.linspace(extent[2], extent[3], 300)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    G = green_function(c, Z)
    
    # Calculate G(0) approximately
    gc0_val = 0
    z_iter = 0
    for n in range(50):
        if abs(z_iter) > 2.1:
            gc0_val = (1.0/(2**n)) * np.log(abs(z_iter))
            break
        z_iter = z_iter**2 + c
        
    fig, ax = plt.subplots(figsize=(6, 6))
    ax.imshow(G, extent=extent, origin='lower', cmap='bone_r', vmax=2.0)
    levels = [0.5, 1.5, 2.0]
    cs = ax.contour(X, Y, G, levels=levels, colors=['red', 'orange', 'blue'])
    ax.clabel(cs, fmt='%.2f')
    ax.plot(0, 0, 'rx', markersize=10, label=f'0 ($G_c(0) > 0$)')
    ax.set_title(f"Eventual Empty ($c \\notin \\mathcal{{M}}$)")
    ax.legend()
    plt.tight_layout()
    plt.savefig('../docs/images/puzzle_empty.png', dpi=150)
    plt.close()

def plot_basic_julia():
    print("Generating basic_julia.png...")
    c = -0.7269 + 0.1889j
    extent = [-1.5, 1.5, -1.5, 1.5]
    x = np.linspace(extent[0], extent[1], 400)
    y = np.linspace(extent[2], extent[3], 400)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    G = green_function(c, Z)
    
    fig, ax = plt.subplots(figsize=(6, 6))
    ax.imshow(G, extent=extent, origin='lower', cmap='bone_r', vmax=1.0)
    ax.contourf(X, Y, G, levels=[0, 0.001], colors=['black'])
    ax.set_title(f"Filled Julia Set $K(c)$ and Boundary $J(c)$ \n$c = {c}$")
    plt.tight_layout()
    plt.savefig('../docs/images/basic_julia.png', dpi=150)
    plt.close()

def plot_basic_mandelbrot():
    print("Generating basic_mandelbrot.png...")
    extent = [-2.0, 1.0, -1.2, 1.2]
    x = np.linspace(extent[0], extent[1], 400)
    y = np.linspace(extent[2], extent[3], 320)
    X, Y = np.meshgrid(x, y)
    C = X + 1j * Y
    
    g_param = np.zeros_like(C, dtype=float)
    escaped = np.zeros_like(C, dtype=bool)
    Zn = np.zeros_like(C, dtype=complex)
    
    for n in range(50):
        mask = (~escaped) & (np.abs(Zn) > 2.0)
        if np.any(mask):
            g_param[mask] = (1.0 / (2**n)) * np.log(np.abs(Zn[mask]))
            escaped[mask] = True
        not_escaped = ~escaped
        Zn[not_escaped] = Zn[not_escaped]**2 + C[not_escaped]
        
    fig, ax = plt.subplots(figsize=(8, 6))
    ax.imshow(g_param, extent=extent, origin='lower', cmap='twilight_shifted', vmax=1.0)
    ax.contourf(X, Y, g_param, levels=[0, 0.001], colors=['black'])
    ax.set_title(r"Mandelbrot Set $\mathcal{M}$")
    plt.tight_layout()
    plt.savefig('../docs/images/basic_mandelbrot.png', dpi=150)
    plt.close()

def plot_escape_radius():
    print("Generating escape_radius.png...")
    c = -0.8 + 0.156j
    R = max(2, 1 + abs(c))
    
    fig, ax = plt.subplots(figsize=(6, 6))
    circle = plt.Circle((0, 0), R, fill=False, color='red', linestyle='--', linewidth=2, label=f'Escape Radius $R(c)={R:.2f}$')
    ax.add_patch(circle)
    
    # Plot a trajectory escaping
    z = 1.1 * R + 0.0j # Start outside
    path_x, path_y = [z.real], [z.imag]
    for _ in range(5):
        z = z**2 + c
        path_x.append(z.real)
        path_y.append(z.imag)
        if abs(z) > 10: break
    
    ax.plot(path_x, path_y, 'b-o', label='Escaping Orbit')
    
    # Plot a bounded trajectory
    z_in = 0.0j
    path_x_in, path_y_in = [z_in.real], [z_in.imag]
    for _ in range(20):
        z_in = z_in**2 + c
        path_x_in.append(z_in.real)
        path_y_in.append(z_in.imag)
    ax.plot(path_x_in, path_y_in, 'g-', alpha=0.5, label='Bounded Orbit (inside)')
    
    ax.set_xlim(-4, 4)
    ax.set_ylim(-4, 4)
    ax.set_aspect('equal')
    ax.set_title(r"Escape Radius $R(c)$")
    ax.legend()
    plt.tight_layout()
    plt.savefig('../docs/images/escape_radius.png', dpi=150)
    plt.close()

if __name__ == "__main__":
    ensure_dir()
    plot_annulus()
    plot_para_puzzle()
    plot_nesting()
    plot_persistence()
    plot_empty()
    plot_basic_julia()
    plot_basic_mandelbrot()
    plot_escape_radius()
