
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, Rectangle

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

def plot_global_context(ax):
    """
    Plots the global view of the Julia set for c=-1 (Basilica)
    and indicates the critical point region.
    """
    # Extent
    extent = [-2.0, 2.0, -1.5, 1.5]
    x = np.linspace(extent[0], extent[1], 400)
    y = np.linspace(extent[2], extent[3], 300)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    
    c = -1.0
    G = green_function(c, Z, max_iter=80)
    
    # Background
    ax.imshow(G, extent=extent, origin='lower', cmap='bone_r', vmax=2.0, alpha=0.4)
    # Julia Set
    ax.contourf(X, Y, G, levels=[0, 0.01], colors=['black'])
    
    # Critical Point
    ax.plot(0, 0, 'ro', label='Critical Point $0$')
    
    # Zoom box around 0
    rect = Rectangle((-0.5, -0.5), 1.0, 1.0, linewidth=2, edgecolor='red', facecolor='none', linestyle='--')
    ax.add_patch(rect)
    
    # Label the zoom
    ax.annotate("Focus Region", xy=(0.5, 0.5), xytext=(1.0, 1.0),
                arrowprops=dict(arrowstyle="->", color='red'), color='red', fontsize=10)
    
    ax.set_title("Global View ($c=-1$)\nThe Critical Point $0$ is deep inside $K(c)$")
    ax.set_aspect('equal')
    ax.set_xlim(extent[0], extent[1])
    ax.set_ylim(extent[2], extent[3])
    ax.legend(loc='upper right', fontsize=8)

def plot_yoccoz_idea(ax):
    """
    Conceptual visualization of Yoccoz's Theorem:
    Puzzle pieces P_0 > P_1 > P_2 ... shrinking to {0}
    because the moduli of the annuli sum to infinity.
    """
    ax.set_aspect('equal')
    ax.set_xlim(-1.5, 1.5)
    ax.set_ylim(-1.5, 1.5)
    ax.axis('off')
    
    # 1. Draw nested puzzle pieces (stylized as shapes)
    # P_0: Large outer shape
    theta = np.linspace(0, 2*np.pi, 200)
    r0 = 1.2 + 0.1 * np.cos(3*theta)
    ax.plot(r0 * np.cos(theta), r0 * np.sin(theta), 'k-', lw=1.5)
    ax.text(0.9, 0.9, '$P_0$', fontsize=12)
    
    # P_1: Inside P_0
    r1 = 0.8 + 0.1 * np.cos(4*theta)
    ax.plot(r1 * np.cos(theta), r1 * np.sin(theta), 'k-', lw=1.5)
    ax.text(0.6, 0.6, '$P_1$', fontsize=12)
    
    # P_2: Inside P_1
    r2 = 0.5 + 0.05 * np.cos(5*theta)
    ax.plot(r2 * np.cos(theta), r2 * np.sin(theta), 'k-', lw=1.5)
    ax.text(0.35, 0.35, '$P_2$', fontsize=12)

    # P_3: Small
    r3 = 0.2 + 0.02 * np.cos(3*theta)
    ax.plot(r3 * np.cos(theta), r3 * np.sin(theta), 'k-', lw=1.5)
    
    # 2. Highlight Annuli
    # Fill A_0 = P_0 \ P_1
    # We can't easily fill complex non-convex shapes with hole in pure matplotlib without polygon logic,
    # but we can fill P_0 with color 1, then fill P_1 with color 2 on top.
    
    ax.fill(r0 * np.cos(theta), r0 * np.sin(theta), color='#e0f3db', alpha=1.0) # Light green
    ax.fill(r1 * np.cos(theta), r1 * np.sin(theta), color='#a8ddb5', alpha=1.0) # Medium green
    ax.fill(r2 * np.cos(theta), r2 * np.sin(theta), color='#43a2ca', alpha=1.0) # Blue
    ax.fill(r3 * np.cos(theta), r3 * np.sin(theta), color='#0868ac', alpha=1.0) # Dark Blue
    
    # 3. The critical point
    ax.plot(0, 0, 'r*', markersize=10, markeredgecolor='white', label='Critical Point $0$')
    
    # 4. Annotations
    ax.annotate("Annulus $A_0$\nmodulus $\mu_0$", xy=(0, 1.0), xytext=(-1.4, 1.2),
                arrowprops=dict(arrowstyle="->", connectionstyle="arc3,rad=0.2"))
                
    ax.annotate("Annulus $A_1$\nmodulus $\mu_1$", xy=(0.6, 0), xytext=(1.0, 0),
                arrowprops=dict(arrowstyle="->", connectionstyle="arc3,rad=-0.2"))
                
    ax.annotate("Intersection\n$\{0\}$", xy=(0, 0), xytext=(-0.5, -0.8),
                arrowprops=dict(arrowstyle="->", color='red'))
                
    ax.set_title("Conceptual Model: Shrinking Puzzle Pieces\n$\sum \mathrm{mod}(A_n) = \infty \\Rightarrow \cap P_n = \{0\}$")

def main():
    fig, axes = plt.subplots(1, 2, figsize=(12, 6))
    
    # Panel 1: Global Context
    plot_global_context(axes[0])
    
    # Panel 2: Conceptual Diagram
    plot_yoccoz_idea(axes[1])
    
    plt.tight_layout()
    plt.savefig('../docs/images/yoccoz_concept.png', dpi=300)
    print("Saved ../docs/images/yoccoz_concept.png")

if __name__ == "__main__":
    main()
