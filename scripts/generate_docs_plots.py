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

def plot_basic_mapping():
    print("Generating basic_mapping.png...")
    c = -1
    # Create grid
    x = np.linspace(-2, 2, 20)
    y = np.linspace(-2, 2, 20)
    
    fig, axes = plt.subplots(1, 2, figsize=(10, 5))
    
    # Domain
    for i in x:
        axes[0].plot([i, i], [-2, 2], 'b-', alpha=0.3)
    for i in y:
        axes[0].plot([-2, 2], [i, i], 'b-', alpha=0.3)
    axes[0].set_title("Domain (z plane)")
    axes[0].set_aspect('equal')
    axes[0].grid(True)
    
    # Image
    for i in x:
        z_line = i + 1j * np.linspace(-2, 2, 100)
        w_line = z_line**2 + c
        axes[1].plot(w_line.real, w_line.imag, 'r-', alpha=0.3)
    for i in y:
        z_line = np.linspace(-2, 2, 100) + 1j * i
        w_line = z_line**2 + c
        axes[1].plot(w_line.real, w_line.imag, 'r-', alpha=0.3)
        
    axes[1].set_title(f"Range ($z \mapsto z^2 + {c}$)")
    axes[1].set_aspect('equal')
    axes[1].grid(True)
    
    plt.tight_layout()
    plt.savefig('../docs/images/basic_mapping.png', dpi=150)
    plt.close()

def plot_basic_connectivity():
    print("Generating basic_connectivity.png...")
    # Connected (c in M)
    c1 = -0.12 + 0.75j
    # Disconnected (c not in M)
    c2 = -0.12 + 0.85j # slightly outside
    
    extent = [-1.5, 1.5, -1.5, 1.5]
    x = np.linspace(extent[0], extent[1], 300)
    y = np.linspace(extent[2], extent[3], 300)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    
    G1 = green_function(c1, Z)
    G2 = green_function(c2, Z)
    
    fig, axes = plt.subplots(1, 2, figsize=(10, 5))
    
    axes[0].imshow(G1, extent=extent, origin='lower', cmap='bone_r', vmax=0.5)
    axes[0].contourf(X, Y, G1, levels=[0, 0.001], colors=['black'])
    axes[0].set_title(f"Connected $K(c)$\n$c={c1} \in \mathcal{{M}}$")
    
    axes[1].imshow(G2, extent=extent, origin='lower', cmap='bone_r', vmax=0.5)
    axes[1].contourf(X, Y, G2, levels=[0, 0.001], colors=['black'])
    axes[1].set_title(f"Disconnected $K(c)$\n$c={c2} \\notin \mathcal{{M}}$")
    
    plt.tight_layout()
    plt.savefig('../docs/images/basic_connectivity.png', dpi=150)
    plt.close()

def plot_escape_growth():
    print("Generating escape_growth.png...")
    c = 0.3
    R = 2.0
    
    fig, ax = plt.subplots(figsize=(6, 4))
    
    # Escaping orbit
    z_esc = 1.5 # Close to escape
    orbit_esc = [abs(z_esc)]
    curr = z_esc
    for _ in range(10):
        curr = curr**2 + c
        orbit_esc.append(abs(curr))
    
    # Bounded orbit
    z_bd = 0.5
    orbit_bd = [abs(z_bd)]
    curr = z_bd
    for _ in range(10):
        curr = curr**2 + c
        orbit_bd.append(abs(curr))
        
    ax.plot(orbit_esc, 'b-o', label='Escaping ($|z_0|=1.5$)')
    ax.plot(orbit_bd, 'g-x', label='Bounded ($|z_0|=0.5$)')
    ax.axhline(R, color='r', linestyle='--', label='Escape Radius R')
    
    ax.set_yscale('log')
    ax.set_xlabel('Iteration n')
    ax.set_ylabel('|z_n| (log scale)')
    ax.set_title("Orbit Growth")
    ax.legend()
    ax.grid(True)
    
    plt.tight_layout()
    plt.savefig('../docs/images/escape_growth.png', dpi=150)
    plt.close()

def plot_green_functional_eq():
    print("Generating green_functional_eq.png...")
    c = -1
    extent = [-2, 2, -2, 2]
    x = np.linspace(extent[0], extent[1], 300)
    y = np.linspace(extent[2], extent[3], 300)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    
    G = green_function(c, Z)
    
    fig, ax = plt.subplots(figsize=(6, 6))
    ax.imshow(G, extent=extent, origin='lower', cmap='gray', vmax=2.0, alpha=0.2)
    
    # Plot Level L
    L = 0.5
    cs1 = ax.contour(X, Y, G, levels=[L], colors=['blue'], linewidths=2)
    ax.clabel(cs1, fmt=f'G={L}')
    
    # Plot Level 2L
    cs2 = ax.contour(X, Y, G, levels=[2*L], colors=['red'], linewidths=2)
    ax.clabel(cs2, fmt=f'G={2*L}')
    
    ax.set_title(r"Functional Eq: $G(f(z)) = 2G(z)$")
    
    # Annotate mapping
    # Pick a point on level L
    # Hard to pick exact point programmatically without solving, just conceptual
    
    plt.tight_layout()
    plt.savefig('../docs/images/green_functional_eq.png', dpi=150)
    plt.close()

def plot_groetzsch_packing():
    print("Generating groetzsch_packing.png...")
    fig, ax = plt.subplots(figsize=(6, 6))
    
    # Draw outer container
    circle_outer = plt.Circle((0, 0), 4, color='black', fill=False, linewidth=2)
    ax.add_patch(circle_outer)
    
    # Draw nested annuli
    radii = [3.5, 3.0, 2.5, 2.0, 1.5, 1.0, 0.5]
    colors = ['#ffcccc', '#ccffcc', '#ccccff', '#ffffcc', '#ffccff', '#ccffff']
    
    for i in range(len(radii)-1):
        # Annulus from radii[i] to radii[i+1] (actually reverse)
        # We draw outer circle filled with color, then inner circle white (or next color)
        # Easier: matplotlib Wedge or just fill_between?
        # Simplest: Draw large filled circles on top of each other
        pass

    # Re-do with simple circles
    # Background
    ax.set_xlim(-4.5, 4.5)
    ax.set_ylim(-4.5, 4.5)
    
    rs = [4.0, 3.5, 3.0, 2.5, 2.0, 1.5, 1.0, 0.5]
    # Annulus 1: 4.0 -> 3.5
    # Annulus 2: 3.0 -> 2.5
    # Gap: 3.5 -> 3.0
    
    # Draw filled rings
    # Ring 1
    circle1 = plt.Circle((0,0), 4.0, color='blue', alpha=0.3)
    ax.add_patch(circle1)
    circle1_in = plt.Circle((0,0), 3.5, color='white')
    ax.add_patch(circle1_in)
    
    # Ring 2
    circle2 = plt.Circle((0,0), 3.0, color='green', alpha=0.3)
    ax.add_patch(circle2)
    circle2_in = plt.Circle((0,0), 2.5, color='white')
    ax.add_patch(circle2_in)
    
    # Ring 3
    circle3 = plt.Circle((0,0), 2.0, color='red', alpha=0.3)
    ax.add_patch(circle3)
    circle3_in = plt.Circle((0,0), 1.5, color='white')
    ax.add_patch(circle3_in)
    
    ax.text(0, 3.75, '$A_1$', ha='center', va='center', fontweight='bold')
    ax.text(0, 2.75, '$A_2$', ha='center', va='center', fontweight='bold')
    ax.text(0, 1.75, '$A_3$', ha='center', va='center', fontweight='bold')
    ax.text(0, 0, '$K$', ha='center', va='center', fontsize=14)
    
    ax.set_aspect('equal')
    ax.axis('off')
    ax.set_title(r"Grötzsch Inequality: $\sum \operatorname{mod}(A_i) \leq \operatorname{mod}(S)$")
    
    plt.tight_layout()
    plt.savefig('../docs/images/groetzsch_packing.png', dpi=150)
    plt.close()

def plot_yoccoz_contradiction():
    print("Generating yoccoz_proof_contradiction.png...")
    # Visualize moduli dropping to zero
    n = np.arange(10)
    moduli_case1 = 1.0 / (n + 1) # Harmonic series, diverges (Case 1)
    moduli_case2 = np.array([1.0, 0.8, 0.5, 0.2, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]) # Becomes 0 (Case 2)
    
    fig, ax = plt.subplots(figsize=(6, 4))
    
    ax.plot(n, moduli_case1, 'b-o', label='Case 1 ($c \in \mathcal{M}$): $\sum \infty$')
    ax.plot(n, moduli_case2, 'r-x', label='Case 2 ($c \\notin \mathcal{M}$): Finite Sum')
    
    ax.axhline(0, color='black', linewidth=0.5)
    ax.set_xlabel('Depth n')
    ax.set_ylabel('Modulus mod($A_n$)')
    ax.set_title("Proof Strategy: Moduli Behavior")
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('../docs/images/yoccoz_proof_contradiction.png', dpi=150)
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
    plot_basic_mapping()
    plot_basic_connectivity()
    plot_escape_growth()
    plot_green_functional_eq()
    plot_groetzsch_packing()
    plot_yoccoz_contradiction()
