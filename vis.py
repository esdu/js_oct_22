import matplotlib.pyplot as plt
from matplotlib import collections as mc


def visualize(name, field, bridges):
    n = len(field)
    m = len(field[0])

    # Create figure and plot islands
    ys = []
    xs = []
    labels = []
    for i in range(n):
        for j in range(m):
            if field[i][j] != 0:
                ys.append(-i)
                xs.append(j)
                labels.append(f"{field[i][j]}")

    fig, ax = plt.subplots()
    ax.autoscale()
    ax.margins(0.1)
    ax.scatter(xs, ys)

    # Label the islands
    for x, y, label in zip(xs, ys, labels):
        ax.annotate(
            label,
            (x, y),
            textcoords="offset points",
            xytext=(0, 10),
            ha='center'
        )

    # Plot the bridges
    singles = [sp for sp in bridges if sp[-1] == 1]
    lines = [[(j, -i), (q, -p)] for (i, j, p, q), _ in singles]
    lc = mc.LineCollection(lines, linewidths=2)
    ax.add_collection(lc)

    doubles = [sp for sp in bridges if sp[-1] == 2]
    lines = [[(j, -i), (q, -p)] for (i, j, p, q), _ in doubles]
    lc = mc.LineCollection(lines, linewidths=6)
    ax.add_collection(lc)

    plt.title(name)
    plt.savefig(f"{name}.png")


if __name__ == "__main__":
    fields = [
        [
            [4, 0, 0, 0, 0, 0, 5, 0, 3, 0, 0, 0, 0, 0, 4, 0, 1],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [6, 0, 2, 0, 0, 0, 5, 0, 5, 0, 0, 0, 4, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 4],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 4],
        ],
        [
            [4, 0, 4, 0, 4, 0, 0, 0, 0, 0, 5, 0, 0, 0, 2, 0, 1],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [3, 0, 2, 0, 4, 0, 0, 0, 4, 0, 4, 0, 0, 0, 5, 0, 3],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [5, 0, 4, 0, 4, 0, 3, 0, 0, 0, 5, 0, 1, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 4, 0, 5, 0, 4],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [3, 0, 4, 0, 5, 0, 0, 0, 2, 0, 4, 0, 2, 0, 2, 0, 4],
        ],
        [
            [4, 0, 4, 0, 2, 0, 0, 0, 2, 0, 4, 0, 0, 0, 4, 0, 2],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [4, 0, 7, 0, 6, 0, 4, 0, 0, 0, 0, 0, 0, 0, 5, 0, 4],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 4, 0, 5, 0, 7, 0, 2, 0, 2, 0, 2],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [1, 0, 0, 0, 3, 0, 0, 1, 0, 0, 4, 0, 0, 0, 4, 0, 2],
        ],
        [
            [4, 0, 2, 0, 3, 0, 4, 0, 0, 0, 5, 0, 5, 0, 0, 0, 4],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 4],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 2],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [3, 0, 4, 0, 6, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 7, 0, 3],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [2, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 3],
        ],
    ]

    solutions = [
        (
            "field_i=0 mislabeled_island=(4, 2)",
            fields[0],
            [((0, 14, 0, 16), 1), ((4, 2, 4, 6), 2), ((2, 8, 4, 8), 1), ((0, 6, 0, 8), 1), ((0, 8, 0, 14), 1), ((10, 8, 10, 12), 2), ((0, 0, 0, 6), 2), ((4, 2, 6, 2), 1), ((0, 0, 4, 0), 2), ((8, 2, 8, 6), 2), ((4, 6, 8, 6), 1), ((12, 14, 12, 16), 2), ((8, 2, 12, 2), 2), ((6, 14, 6, 16), 2), ((0, 14, 6, 14), 2), ((0, 8, 2, 8), 1), ((12, 2, 12, 14), 1), ((6, 2, 8, 2), 2), ((4, 0, 4, 2), 2), ((4, 12, 10, 12), 2), ((4, 8, 4, 12), 2), ((6, 16, 12, 16), 2), ((4, 8, 10, 8), 2), ((6, 14, 12, 14), 2), ((0, 6, 4, 6), 2), ((4, 0, 10, 0), 2)]
        ),
        (
            "field_i=1 mislabeled_island=(6, 12)",
            fields[1],
            [((0, 2, 2, 2), 2), ((0, 14, 4, 14), 1), ((0, 10, 0, 14), 1), ((6, 0, 10, 0), 2), ((2, 12, 6, 12), 1), ((6, 6, 6, 10), 1), ((4, 14, 8, 14), 2), ((10, 2, 12, 2), 2), ((6, 4, 12, 4), 2), ((12, 0, 12, 2), 1), ((8, 12, 8, 14), 1), ((6, 4, 6, 6), 2), ((6, 10, 8, 10), 2), ((0, 4, 4, 4), 2), ((4, 14, 4, 16), 2), ((6, 0, 6, 2), 2), ((0, 0, 4, 0), 2), ((8, 10, 8, 12), 2), ((8, 10, 12, 10), 2), ((0, 0, 0, 2), 2), ((2, 2, 4, 2), 2), ((12, 10, 12, 12), 2), ((4, 4, 4, 8), 2), ((0, 4, 0, 10), 2), ((12, 14, 12, 16), 2), ((12, 2, 12, 4), 1), ((6, 2, 10, 2), 2), ((8, 14, 8, 16), 2), ((10, 0, 10, 2), 2), ((10, 0, 12, 0), 2), ((4, 8, 4, 10), 2), ((6, 12, 8, 12), 1), ((8, 16, 12, 16), 2), ((12, 4, 12, 8), 2), ((0, 10, 4, 10), 2), ((6, 10, 6, 12), 2), ((4, 0, 6, 0), 1), ((0, 16, 4, 16), 1)]
        ),
        (
            "field_i=2 mislabeled_island=(6, 4)",
            fields[2],
            [((0, 2, 2, 2), 2), ((0, 14, 0, 16), 1), ((0, 14, 4, 14), 1), ((6, 14, 8, 14), 2), ((4, 4, 6, 4), 1), ((8, 8, 8, 10), 1), ((6, 4, 12, 4), 2), ((4, 6, 8, 6), 2), ((0, 16, 2, 16), 1), ((0, 4, 4, 4), 2), ((4, 14, 4, 16), 2), ((8, 10, 10, 10), 2), ((4, 2, 4, 4), 1), ((4, 2, 10, 2), 2), ((0, 0, 4, 0), 2), ((12, 10, 12, 14), 2), ((0, 8, 8, 8), 2), ((8, 10, 8, 12), 2), ((0, 0, 0, 2), 2), ((2, 2, 4, 2), 2), ((4, 16, 8, 16), 2), ((4, 14, 6, 14), 2), ((2, 10, 8, 10), 2), ((12, 14, 12, 16), 2), ((8, 6, 8, 8), 2), ((10, 0, 10, 2), 2), ((4, 0, 4, 2), 2), ((0, 10, 0, 14), 2), ((0, 10, 2, 10), 2), ((12, 4, 12, 7), 1), ((4, 4, 4, 6), 2), ((10, 10, 12, 10), 2), ((10, 0, 12, 0), 1)]
        ),
        (
            "field_i=3 mislabeled_island=(10, 10)",
            fields[3],
            [((10, 14, 12, 14), 2), ((0, 12, 4, 12), 2), ((12, 0, 12, 4), 1), ((0, 10, 0, 12), 1), ((8, 4, 8, 8), 2), ((8, 0, 8, 2), 2), ((0, 4, 8, 4), 2), ((2, 10, 6, 10), 2), ((0, 6, 2, 6), 1), ((0, 12, 0, 16), 2), ((4, 2, 8, 2), 2), ((8, 0, 12, 0), 1), ((2, 6, 2, 10), 2), ((10, 10, 10, 12), 1), ((0, 0, 4, 0), 2), ((10, 16, 12, 16), 1), ((0, 0, 0, 2), 2), ((10, 12, 10, 14), 1), ((2, 6, 6, 6), 2), ((12, 14, 12, 16), 2), ((6, 14, 6, 16), 2), ((0, 16, 4, 16), 2), ((4, 12, 4, 16), 2), ((4, 0, 4, 2), 2), ((4, 12, 10, 12), 2), ((0, 10, 2, 10), 2), ((6, 6, 6, 10), 2), ((8, 8, 12, 8), 2), ((0, 4, 0, 6), 1), ((10, 14, 10, 16), 2), ((6, 14, 10, 14), 2), ((0, 6, 0, 10), 2), ((8, 4, 12, 4), 2)]
        )
    ]
    
    for name, field, bridges in solutions:
        visualize(name, field, bridges)
