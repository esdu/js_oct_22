import copy
from collections import defaultdict
from typing import List


def get_islands(field):
    islands = []
    for i in range(len(field)):
        for j in range(len(field[i])):
            if field[i][j] != 0:
                islands.append((i, j))
    return islands


def combo(iter1, iter2):
    for item1 in iter1:
        for item2 in iter2:
            yield item1, item2


def hv_bridges_intersect(hb, vb) -> bool:
    """
    This checks the intersection between a pair of horizontal and vertical bridges.
    hb: horizontal bridge
    vb: vertical bridge
    NOTE: bridges are considered _open_ on both ends (i.e. they don't include the ending islands).
          i.e. if one bridge's ending island lies on another bridge, it's not an intersection.
    Returns True if the two bridges intersect.

    Visualization for algo:
                        |                   < v_min_i
                        |
                        |
                 ----------------           < h_i
                        |
                        |
                        |                   < v_max_i
         h_min_j ^      ^ v_j   ^ h_max_j
    """
    i, j, p, q = hb
    ii, jj, pp, qq = vb

    h_min_j = min(j, q)
    h_max_j = max(j, q)
    h_i = i

    v_min_i = min(ii, pp)
    v_max_i = max(ii, pp)
    v_j = jj

    return h_min_j < v_j and v_j < h_max_j and v_min_i < h_i and h_i < v_max_i


assert hv_bridges_intersect((5, 0, 5, 10), (4, 2, 7, 2)) == True
assert hv_bridges_intersect((5, 2, 5, 10), (4, 2, 7, 2)) == False
assert hv_bridges_intersect((4, 2, 4, 10), (4, 2, 7, 2)) == False
assert hv_bridges_intersect((5, 0, 5, 10), (4, 12, 7, 12)) == False
assert hv_bridges_intersect((5, 0, 5, 10), (2, 0, 2, 8)) == False


def get_bridge_combinations(bridges, num_bridges) -> List[List[tuple]]:
    """Return all ways of selecting num_bridges from bridges,
    where each bridge can be 1-wide or 2-wide."""
    if num_bridges == 0:
        return []

    if not bridges:
        return []

    if num_bridges == 1:
        use_zero = get_bridge_combinations(bridges[1:], num_bridges)
        use_one = [[(bridges[0], 1)]]
        return use_zero + use_one

    if num_bridges == 2:
        use_zero = get_bridge_combinations(bridges[1:], num_bridges)
        use_one = [[(bridges[0], 1)] + ls
                   for ls in get_bridge_combinations(bridges[1:], num_bridges-1)]
        use_two = [[(bridges[0], 2)]]
        return use_zero + use_one + use_two

    use_zero = get_bridge_combinations(bridges[1:], num_bridges)
    use_one = [[(bridges[0], 1)] + ls
               for ls in get_bridge_combinations(bridges[1:], num_bridges-1)]
    use_two = [[(bridges[0], 2)] + ls
               for ls in get_bridge_combinations(bridges[1:], num_bridges-2)]
    return use_zero + use_one + use_two


def combine_bridge_combos(combos1: List[List[tuple]], combos2: List[List[tuple]], is_intersect_fn, is_impossible_fn) -> List[List[tuple]]:
    if not combos1:
        return combos2
    if not combos2:
        return combos1

    new_combos = []

    for bridges1, bridges2 in combo(combos1, combos2):
        # If any pair of bridges are intersecting, it would not be a valid combination.
        if any(is_intersect_fn(b1, b2)
               for (b1, _), (b2, _) in combo(bridges1, bridges2)):
            continue

        # If a bridge is used twice, like (b1, 1) and (b1, 2), it's only valid if the widths are equal.
        if any(b1 == b2 and (w1 != w2)
               for (b1, w1), (b2, w2) in combo(bridges1, bridges2)):
            continue

        # Combine and dedupe any common bridges
        new_bridges = list(set(bridges1+bridges2))

        # If this breaks any constraints, it's not a valid combination.
        if is_impossible_fn(new_bridges):
            continue

        new_combos.append(new_bridges)

    return new_combos


def impossible_given_mislabeled_island(
        field, island_to_bridges, combo, mislabeled_island, debug=False) -> bool:
    """Is it impossiblem given x is the mislabeled island?"""

    # We subtract 1 from each field[i][j] where (i, j) island has a bridge.
    # Combo could be impossible if any field[i][j] dips below 0.
    remaining_field = copy.deepcopy(field)

    # Optimization (3x speedup)
    # If any field[i][j] becomes 0, then any remaining bridges connected to island (i, j) cannot be used.
    # If remaining bridges cannot possibly be enough for any remaining island, then this combo is impossible.
    remaining_outs = copy.deepcopy(island_to_bridges)

    def check_outs(i, j):
        nonlocal remaining_field, remaining_outs

        if (i, j) != mislabeled_island and remaining_field[i][j] == 0:
            for bridge in island_to_bridges[(i, j)]:
                ii, jj, pp, qq = bridge

                if bridge in remaining_outs[(ii, jj)]:
                    remaining_outs[(ii, jj)].remove(bridge)
                if bridge in remaining_outs[(pp, qq)]:
                    remaining_outs[(pp, qq)].remove(bridge)

                # if there aren't enough possible bridges to satisfy this island, it's impossible.
                # note the "*2" is assuming all bridges has at most width 2
                if (ii, jj) != mislabeled_island and len(remaining_outs[(ii, jj)])*2 < remaining_field[ii][jj]:
                    return True
                if (pp, qq) != mislabeled_island and len(remaining_outs[(pp, qq)])*2 < remaining_field[pp][qq]:
                    return True

        return False

    for (i, j, p, q), width in combo:
        remaining_field[i][j] -= width
        remaining_field[p][q] -= width

        # Check if any field[i][j] dips below 0.
        if (i, j) != mislabeled_island and remaining_field[i][j] < 0:
            return True
        if (p, q) != mislabeled_island and remaining_field[p][q] < 0:
            return True

        # remove bridges from island that have been used up already from the "outs"
        if check_outs(i, j) or check_outs(p, q):
            return True

    return False


def verify_solution(field, bridges):
    # There are a couple of constraints our algo didn't check yet.

    # (1) Check there is exactly 1 connected component (Hashi's rule)
    #     i.e. all islands should be touched by a floodfill
    islands = get_islands(field)

    touched_islands = set()
    q = set()
    q.add(islands[0])  # start at any island

    while q:
        i, j = q.pop()
        touched_islands.add((i, j))
        for (ii, jj, pp, qq), _ in bridges:
            if (i, j) == (ii, jj) and (pp, qq) not in touched_islands:
                q.add((pp, qq))
            if (i, j) == (pp, qq) and (ii, jj) not in touched_islands:
                q.add((ii, jj))

    if len(touched_islands) != len(islands):
        return False

    # (2) Check there is exactly 1 mislabeled island
    remaining_field = copy.deepcopy(field)
    for (i, j, p, q), width in bridges:
        remaining_field[i][j] -= width
        remaining_field[p][q] -= width

    mislabeled_islands = 0
    for i in range(len(remaining_field)):
        for j in range(len(remaining_field[0])):
            if remaining_field[i][j] != 0:
                mislabeled_islands += 1

    if mislabeled_islands != 1:
        return False

    return True


def work(task):
    field, field_i, mislabeled_island = task
    print(f"field_i={field_i} mislabeled_island={mislabeled_island}")

    n = len(field)
    m = len(field[0])

    # Horizontal bridges go from left to right
    h_bridges = []
    for i in range(n):
        prev_island = None
        for j in range(m):
            if field[i][j] != 0:
                if prev_island is not None:
                    h_bridges.append((prev_island[0], prev_island[1], i, j))
                prev_island = (i, j)

    # Vertical bridges go from top to bottom
    v_bridges = []
    for j in range(m):
        prev_island = None
        for i in range(n):
            if field[i][j] != 0:
                if prev_island is not None:
                    v_bridges.append((prev_island[0], prev_island[1], i, j))
                prev_island = (i, j)

    # Map from each island to all the bridges that could extend from there
    island_to_bridges = defaultdict(set)
    for br in h_bridges + v_bridges:
        i, j, p, q = br
        island_to_bridges[(i, j)].add(br)
        island_to_bridges[(p, q)].add(br)

    # Map from each island to a list of combinations of bridges that would satisfy the island number.
    # Each "bridge" here also includes the "width", which could be 1 or 2.
    # For example, say the island (0, 1) has a number of 2.
    #   bridge_combos[(0, 1)] = [ [((0, 1, 0, 2), 2)] , [((0, 1, 4, 1), 1), ((0, 1, 0, 2), 1)] ]
    # means the island (0, 1) could either have
    #   a 2-wide bridge (0, 1, 0, 2), or
    #   a 1-wide bridge (0, 1, 4, 1) and a 1-wide bridge (0, 1, 0, 2)
    bridge_combos = defaultdict(list)
    for i, j in island_to_bridges:
        bridge_combos[(i, j)] = get_bridge_combinations(
            list(island_to_bridges[(i, j)]), num_bridges=field[i][j])

    # Index of which bridges intersect. Note by construction, only horizontal and vertical bridges can intersect.
    bridge_intersections = defaultdict(set)
    for hb in h_bridges:
        for vb in v_bridges:
            if hv_bridges_intersect(hb, vb):
                bridge_intersections[hb].add(vb)
                bridge_intersections[vb].add(hb)

    # `valid_combos` is the list of combinations of bridges that satisfies all the islands seen so far.
    valid_combos = []
    for next_island in island_to_bridges:
        if next_island == mislabeled_island:
            continue
        valid_combos = combine_bridge_combos(
            valid_combos, bridge_combos[next_island],
            is_intersect_fn=lambda b1, b2: b2 in bridge_intersections[b1],
            is_impossible_fn=lambda combo: impossible_given_mislabeled_island(
                field, island_to_bridges, combo, mislabeled_island))
        if not valid_combos:
            break

    # If any possibiles remain, they're potential solutions.
    for combo in valid_combos:
        if verify_solution(field, combo):
            print(f"🎉 field_i={field_i} mislabeled_island={mislabeled_island}")
            print(combo)


if __name__ == '__main__':
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

    import time
    start = time.perf_counter()

    tasks = []
    for field_i, field in enumerate(fields):
        for island in get_islands(field):
            tasks.append((field, field_i, island))

    import multiprocessing
    with multiprocessing.Pool() as pool:
        pool.map(work, tasks)

    print("total time", time.perf_counter() - start)

    # It turns out the mislabeld islands are:
    # 4, 2
    # 6, 12
    # 6, 4
    # 10, 10
