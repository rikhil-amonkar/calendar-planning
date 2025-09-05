import json
from copy import deepcopy

class ZebraCSP:
    def __init__(self, categories, n_houses):
        self.categories = categories
        self.n = n_houses
        # key is (category, value)
        self.keys = []
        for cat, vals in categories.items():
            for v in vals:
                self.keys.append((cat, v))
        # Domains
        self.domains = {k: set(range(1, n_houses + 1)) for k in self.keys}
        # Equality management via union-find
        self.parent = {k: k for k in self.keys}
        self.group_members = None  # built when needed
        # Constraints
        self.left_rels = []   # list of dicts: {'A':keyA,'B':keyB,'min':m,'max':M}
        self.dist_eq = []     # list of tuples: (keyA, keyB, distance)

    # Union-Find operations for equalities
    def find(self, x):
        if self.parent[x] != x:
            self.parent[x] = self.find(self.parent[x])
        return self.parent[x]

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return
        self.parent[rb] = ra
        self.group_members = None  # invalidate cache

    def build_groups(self):
        if self.group_members is not None:
            return
        groups = {}
        for k in self.keys:
            r = self.find(k)
            groups.setdefault(r, set()).add(k)
        self.group_members = groups

    def add_equality(self, ka, kb):
        self.union(ka, kb)

    def add_left_of(self, ka, kb, min_offset=1, max_offset=None):
        self.left_rels.append({'A': ka, 'B': kb, 'min': min_offset, 'max': max_offset})

    def add_distance(self, ka, kb, distance):
        self.dist_eq.append((ka, kb, distance))

    def set_exact_pos(self, k, pos):
        # Restrict domain to a single position
        self.domains[k] = {pos}

    def remove_pos(self, k, pos):
        if pos in self.domains[k]:
            self.domains[k].remove(pos)

    def category_keys(self, category):
        return [k for k in self.keys if k[0] == category]

    def propagate(self):
        # Main propagation loop
        changed = True
        while changed:
            changed = False
            # Equality propagation: intersect domains within each equivalence class
            self.build_groups()
            for root, members in self.group_members.items():
                # intersection of domains
                inter = set(range(1, self.n + 1))
                for m in members:
                    inter &= self.domains[m]
                if not inter:
                    return False
                for m in members:
                    if self.domains[m] != inter:
                        self.domains[m] = set(inter)
                        changed = True

            # All-different within each category for assigned singles
            for cat, vals in self.categories.items():
                cat_keys = self.category_keys(cat)
                singles = [next(iter(self.domains[k])) for k in cat_keys if len(self.domains[k]) == 1]
                for k in cat_keys:
                    if len(self.domains[k]) > 1:
                        before = set(self.domains[k])
                        self.domains[k] -= set(singles)
                        if not self.domains[k]:
                            return False
                        if self.domains[k] != before:
                            changed = True

            # Left-of propagation
            for rel in self.left_rels:
                A, B = rel['A'], rel['B']
                min_off = rel['min']
                max_off = rel['max']

                domA = self.domains[A]
                domB = self.domains[B]

                # Allowed sets
                newA = set()
                for p in domA:
                    ok = False
                    for q in domB:
                        d = q - p
                        if d >= min_off and (max_off is None or d <= max_off):
                            ok = True
                            break
                    if ok:
                        newA.add(p)
                if not newA:
                    return False
                if newA != domA:
                    self.domains[A] = newA
                    changed = True

                domA = self.domains[A]  # refresh after potential change

                newB = set()
                for q in domB:
                    ok = False
                    for p in domA:
                        d = q - p
                        if d >= min_off and (max_off is None or d <= max_off):
                            ok = True
                            break
                    if ok:
                        newB.add(q)
                if not newB:
                    return False
                if newB != domB:
                    self.domains[B] = newB
                    changed = True

            # Distance-equality propagation
            for (A, B, d) in self.dist_eq:
                domA = self.domains[A]
                domB = self.domains[B]
                newA = set(p for p in domA if (p + d in domB) or (p - d in domB))
                if not newA:
                    return False
                if newA != domA:
                    self.domains[A] = newA
                    changed = True

                domA = self.domains[A]
                domB = self.domains[B]
                newB = set(q for q in domB if (q + d in domA) or (q - d in domA))
                if not newB:
                    return False
                if newB != domB:
                    self.domains[B] = newB
                    changed = True

        return True

    def is_solved(self):
        return all(len(self.domains[k]) == 1 for k in self.keys)

    def choose_unassigned_key(self):
        # Choose a representative key per equality group to reduce branching
        self.build_groups()
        # Build a set of representative keys (group roots)
        reps = []
        for root, members in self.group_members.items():
            # domains are equal among members; pick any
            k = next(iter(members))
            if len(self.domains[k]) > 1:
                reps.append(k)
        if not reps:
            return None
        reps.sort(key=lambda k: len(self.domains[k]))
        return reps[0]

    def assign(self, k, pos):
        # Assign position pos to the entire equality group of key k
        root = self.find(k)
        for m in self.group_members[root]:
            self.domains[m] = {pos}

    def solve(self):
        if not self.propagate():
            return None
        if self.is_solved():
            return self.domains
        k = self.choose_unassigned_key()
        if k is None:
            return None
        # Try each position in domain
        for pos in sorted(self.domains[k]):
            saved_domains = deepcopy(self.domains)
            # equality groups need to be built to assign group-wise
            self.build_groups()
            saved_groups = deepcopy(self.group_members)
            try:
                self.assign(k, pos)
                if self.propagate():
                    res = self.solve()
                    if res is not None:
                        return res
            finally:
                self.domains = saved_domains
                self.group_members = saved_groups
        return None


def main():
    n = 6
    categories = {
        "Name": ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"],
        "Cigar": ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"],
        "MusicGenre": ["hip hop", "jazz", "country", "pop", "classical", "rock"],
        "Drink": ["water", "milk", "boba tea", "tea", "root beer", "coffee"],
        "Mother": ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"],
        "Food": ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"],
    }

    def K(cat, val):
        return (cat, val)

    csp = ZebraCSP(categories, n)

    # Clues encoding

    # 1. Carol is directly left of the person who loves eating grilled cheese.
    csp.add_left_of(K("Name", "Carol"), K("Food", "grilled cheese"), min_offset=1, max_offset=1)

    # 2. Eric is not in the second house.
    csp.remove_pos(K("Name", "Eric"), 2)

    # 3. The person whose mother's name is Holly is somewhere to the right of Carol.
    csp.add_left_of(K("Name", "Carol"), K("Mother", "Holly"), min_offset=1, max_offset=None)

    # 4. Grilled cheese is somewhere to the right of rock music.
    csp.add_left_of(K("MusicGenre", "rock"), K("Food", "grilled cheese"), min_offset=1, max_offset=None)

    # 5. Eric is directly left of Carol.
    csp.add_left_of(K("Name", "Eric"), K("Name", "Carol"), min_offset=1, max_offset=1)

    # 6. Pop music is not in the third house.
    csp.remove_pos(K("MusicGenre", "pop"), 3)

    # 7. Eric is the person who loves country music.
    csp.add_equality(K("Name", "Eric"), K("MusicGenre", "country"))

    # 8. The person who loves classical music is in the sixth house.
    csp.set_exact_pos(K("MusicGenre", "classical"), 6)

    # 9. The coffee drinker is Bob.
    csp.add_equality(K("Drink", "coffee"), K("Name", "Bob"))

    # 10. The person who smokes many unique blends is Peter.
    csp.add_equality(K("Cigar", "blends"), K("Name", "Peter"))

    # 11. The person who loves the stew is not in the fifth house.
    csp.remove_pos(K("Food", "stew"), 5)

    # 12. The root beer lover is directly left of The person whose mother's name is Janelle.
    csp.add_left_of(K("Drink", "root beer"), K("Mother", "Janelle"), min_offset=1, max_offset=1)

    # 13. There are two houses between Sarah and Yellow Monster.
    csp.add_distance(K("Mother", "Sarah"), K("Cigar", "yellow monster"), distance=3)

    # 14. Eric is the tea drinker.
    csp.add_equality(K("Name", "Eric"), K("Drink", "tea"))

    # 15. Pall Mall is somewhere to the right of stir fry.
    csp.add_left_of(K("Food", "stir fry"), K("Cigar", "pall mall"), min_offset=1, max_offset=None)

    # 16. The person who loves the soup is Bob.
    csp.add_equality(K("Food", "soup"), K("Name", "Bob"))

    # 17. Hip-hop music is directly left of Kailyn.
    csp.add_left_of(K("MusicGenre", "hip hop"), K("Mother", "Kailyn"), min_offset=1, max_offset=1)

    # 18. Arnold is somewhere to the right of Kailyn.
    csp.add_left_of(K("Mother", "Kailyn"), K("Name", "Arnold"), min_offset=1, max_offset=None)

    # 19. Water is directly left of Blue Master.
    csp.add_left_of(K("Drink", "water"), K("Cigar", "blue master"), min_offset=1, max_offset=1)

    # 20. The spaghetti eater is somewhere to the left of the person who smokes blends.
    csp.add_left_of(K("Food", "spaghetti"), K("Cigar", "blends"), min_offset=1, max_offset=None)

    # 21. Sarah is directly left of jazz music.
    csp.add_left_of(K("Mother", "Sarah"), K("MusicGenre", "jazz"), min_offset=1, max_offset=1)

    # 22. Hip-hop is directly left of root beer.
    csp.add_left_of(K("MusicGenre", "hip hop"), K("Drink", "root beer"), min_offset=1, max_offset=1)

    # 23. Water drinker is the stew lover.
    csp.add_equality(K("Drink", "water"), K("Food", "stew"))

    # 24. The Dunhill smoker is not in the second house.
    csp.remove_pos(K("Cigar", "dunhill"), 2)

    # 25. The person who likes milk is mother Janelle.
    csp.add_equality(K("Drink", "milk"), K("Mother", "Janelle"))

    # 26. Eric is mother Aniya.
    csp.add_equality(K("Name", "Eric"), K("Mother", "Aniya"))

    # Derived equality from 17 and 22: Kailyn's house equals Root Beer house
    csp.add_equality(K("Mother", "Kailyn"), K("Drink", "root beer"))

    # Solve
    solution_domains = csp.solve()
    if solution_domains is None:
        raise RuntimeError("No solution found")

    # Build output rows
    header = ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"]
    rows = []
    # Invert mapping for each category
    pos_to_val = {cat: {i: None for i in range(1, n + 1)} for cat in categories}
    for (cat, val), dom in solution_domains.items():
        pos = next(iter(dom))
        pos_to_val[cat][pos] = val

    for i in range(1, n + 1):
        row = [
            str(i),
            pos_to_val["Name"][i],
            pos_to_val["Cigar"][i],
            pos_to_val["MusicGenre"][i],
            pos_to_val["Drink"][i],
            pos_to_val["Mother"][i],
            pos_to_val["Food"][i],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()