
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

def plot_puzzle_pieces(c, ax, title):
    # Zoom in near critical point 0
    x = np.linspace(-1.5, 1.5, 500)
    y = np.linspace(-1.2, 1.2, 500)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    
    G = green_function(c, Z, max_iter=60)
    
    # Levels 1/2^n
    levels = [(1.0 / (2**n)) for n in range(0, 4)]
    levels.reverse() # Plot from largest (smallest n) to smallest (largest n)
    
    # We want to show P_0, P_1, P_2 around 0
    # P_n(0) is the component of {G < 1/2^n} containing 0.
    # For Basilica (c=-1), these are nice regions.
    
    # Plot background
    ax.imshow(G, extent=[-1.5, 1.5, -1.2, 1.2], origin='lower', cmap='Greys', vmax=1.0, alpha=0.3)
    
    colors = ['#fee0d2', '#fc9272', '#de2d26', '#a50f15'] # Light to dark red
    
    # Plot filled regions for P_0, P_1, P_2
    # Since 0 is in K(c), G(0)=0. The component around 0 is just the central blob.
    # We can just contourf G < level.
    # Note: matplotlib contourf might pick up other components, but visually it's fine 
    # as long as we focus on 0.
    
    for i, level in enumerate(levels):
        # We want to layer them. P_0 is biggest.
        # So we should plot P_0 first, then P_1 on top, etc.
        # But levels is reversed: small level (P_large_n) first?
        # No, levels is [1/8, 1/4, 1/2, 1].
        # 1/8 is P_3 (smallest).
        # We want to plot P_0 (level 1) first (largest area).
        pass

    # Re-define levels for plotting order: 1, 1/2, 1/4
    plot_levels = sorted([1.0, 0.5, 0.25, 0.125])
    
    # Plot contours boundaries
    ax.contour(X, Y, G, levels=plot_levels, colors='black', linewidths=0.8)
    
    # Label pieces
    # P_0: G < 1
    # P_1: G < 0.5
    # P_2: G < 0.25
    
    # We can't easily isolate the component in matplotlib without image processing,
    # but for c=-1 the components are well separated or clear enough.
    
    ax.text(0, 0, '$0$', ha='center', va='center', fontweight='bold')
    
    # Annotate annulus
    # Point in P_1 \ P_2
    # e.g. G approx 0.3-0.4
    ax.text(0.6, 0.0, '$P_0 \setminus P_1$', ha='center', fontsize=8)
    
    ax.set_title(title)
    ax.set_aspect('equal')

def main():
    fig, ax = plt.subplots(figsize=(8, 6))
    
    # Basilica c = -1
    plot_puzzle_pieces(-1, ax, "Puzzle Pieces for $c=-1$ (Basilica)")
    
    plt.tight_layout()
    plt.savefig('../docs/images/puzzle_pieces.png', dpi=300)
    print("Saved ../docs/images/puzzle_pieces.png")

if __name__ == "__main__":
    main()
