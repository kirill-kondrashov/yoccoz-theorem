
import numpy as np
import matplotlib.pyplot as plt

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

def plot_view(c, ax, extent, title, add_labels=False):
    x = np.linspace(extent[0], extent[1], 500)
    y = np.linspace(extent[2], extent[3], 500)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    
    G = green_function(c, Z, max_iter=60)
    
    # Plot background potential
    ax.imshow(G, extent=extent, origin='lower', cmap='Greys', vmax=1.5, alpha=0.3)
    
    # Plot filled Julia set approximation
    ax.contourf(X, Y, G, levels=[0, 0.02], colors=['#555555'])
    
    # Contours for puzzle pieces levels 1/2^n
    # levels: 1.0 (n=0), 0.5 (n=1), 0.25 (n=2), 0.125 (n=3)
    plot_levels = sorted([1.0, 0.5, 0.25, 0.125])
    
    # Use different colors/styles for contours to distinguish depth
    cs = ax.contour(X, Y, G, levels=plot_levels, colors='black', linewidths=0.8)
    
    if add_labels:
        ax.text(0, 0, '$0$', ha='center', va='center', fontweight='bold', color='white')
        # Label P_0 \ P_1
        # P_0 is G < 1. P_1 is G < 0.5.
        # So region between 0.5 and 1.0
        # In zoomed view (extent ~ 1.5), we can place it.
        # For Basilica c=-1, critical point is 0. Critical value -1.
        # Another component of P_1 is around -1? No P_n(0) is component containing 0.
        
        # Just simple labels
        pass
        
    ax.set_title(title)
    ax.set_aspect('equal')
    ax.set_xlim(extent[0], extent[1])
    ax.set_ylim(extent[2], extent[3])

def main():
    fig, axes = plt.subplots(1, 2, figsize=(12, 6))
    
    # Basilica c = -1
    # Global View
    plot_view(-1, axes[0], [-2.0, 2.0, -1.5, 1.5], "Global View\n$P_0$ (outer), $K(c)$ (dark)")
    
    # Add a box showing the zoom region
    from matplotlib.patches import Rectangle
    rect = Rectangle((-1.2, -1.0), 2.4, 2.0, linewidth=1.5, edgecolor='r', facecolor='none', linestyle='--')
    axes[0].add_patch(rect)
    axes[0].text(-1.1, -0.9, "Zoom", color='red', fontsize=10)
    
    # Zoomed View
    plot_view(-1, axes[1], [-1.2, 1.2, -1.0, 1.0], "Zoomed View near $z=0$\nNested Pieces $P_0 \supset P_1 \supset P_2 \dots$", add_labels=True)
    
    plt.tight_layout()
    plt.savefig('../docs/images/puzzle_pieces.png', dpi=300)
    print("Saved ../docs/images/puzzle_pieces.png")

if __name__ == "__main__":
    main()
