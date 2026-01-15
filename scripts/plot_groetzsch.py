
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, Annulus

def plot_groetzsch(ax, title, radii, center_label):
    ax.set_aspect('equal')
    ax.set_title(title)
    ax.set_xlim(-1.2, 1.2)
    ax.set_ylim(-1.2, 1.2)
    ax.axis('off')
    
    # Draw P_0 outline
    p0 = Circle((0, 0), radii[0], fill=False, color='black', linestyle='--')
    ax.add_patch(p0)
    ax.text(0, radii[0] + 0.05, '$P_0$', ha='center')

    # Draw annuli
    colors = plt.cm.Blues(np.linspace(0.2, 0.8, len(radii)-1))
    
    for i in range(len(radii)-1):
        # Annulus A_i = P_i \ P_{i+1}
        # In matplotlib Annulus takes (center), outer_radius, width
        r_outer = radii[i]
        r_inner = radii[i+1]
        width = r_outer - r_inner
        
        ann = Annulus((0, 0), r_outer, width, color=colors[i], alpha=0.6)
        ax.add_patch(ann)
        
        # Label a few
        if i < 2:
            mid_r = (r_outer + r_inner) / 2
            ax.text(mid_r * 0.707, mid_r * 0.707, f'$A_{i}$', color='black', ha='center', va='center')

    # Draw the limit set K
    k_radius = radii[-1]
    if k_radius > 0:
        k_circle = Circle((0, 0), k_radius, color='red', alpha=0.7)
        ax.add_patch(k_circle)
        ax.text(0, 0, center_label, color='white', ha='center', va='center', fontweight='bold')
    else:
        ax.plot(0, 0, 'ro', markersize=5)
        ax.text(0.05, 0.05, center_label, color='red', ha='left', va='bottom')

def main():
    fig, axes = plt.subplots(1, 2, figsize=(10, 5))
    
    # Case 1: Non-trivial intersection K (Sum of moduli < infinity)
    # Radii converging to R > 0
    # e.g. r_n = 0.5 + 0.5 / 2^n
    radii_1 = [0.5 + 0.5 / (2**n) for n in range(6)]
    radii_1.append(0.5) # The limit K
    
    plot_groetzsch(axes[0], 
                   "Non-trivial Intersection ($K$ is a disk)\n$\sum \mathrm{mod}(A_n) < \infty$", 
                   radii_1, 
                   "$K$")
    
    # Case 2: Trivial intersection {0} (Sum of moduli = infinity)
    # Radii converging to 0 slowly enough to have infinite modulus sum
    # mod(A_n) = log(r_n / r_{n+1})
    # If r_n = 1 / sqrt(n+1), then r_n/r_{n+1} -> 1, but we can just show geometric shrinking to 0
    # Let's just visually show shrinking to 0
    radii_2 = [1.0 / (1.5**n) for n in range(8)]
    radii_2.append(0.0) # Limit is point
    
    plot_groetzsch(axes[1], 
                   "Trivial Intersection ($K=\{0\}$)\n$\sum \mathrm{mod}(A_n) = \infty$", 
                   radii_2, 
                   "$\{0\}$")

    plt.tight_layout()
    plt.savefig('../docs/images/groetzsch_viz.png', dpi=300, bbox_inches='tight')
    print("Saved ../docs/images/groetzsch_viz.png")

if __name__ == "__main__":
    main()
