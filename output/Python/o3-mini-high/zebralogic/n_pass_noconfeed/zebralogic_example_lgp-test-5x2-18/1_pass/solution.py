import itertools
import json

def main():
    # Houses are numbered 1 to 5 (left to right).
    # Parent names and children names lists.
    parents = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    all_children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]
    
    # Fixed assignment from clue 3 and clue 7:
    # - The child "Fred" is in the second house.
    # - The child "Bella" is in the third house.
    #
    # For the remaining houses (house 1, 4, and 5) we will assign a permutation of the remaining children.
    remaining_children = ["Timothy", "Meredith", "Samantha"]
    
    solution = None

    for parent_perm in itertools.permutations(parents):
        # Constraint 5: Eric is not in the third house.
        # Constraint 6: Bob is not in the third house.
        if parent_perm[2] in {"Eric", "Bob"}:
            continue

        for perm in itertools.permutations(remaining_children):
            # Build the children assignment for houses 1 to 5.
            # House indices: 0 -> house1, 1 -> house2, 2 -> house3, 3 -> house4, 4 -> house5.
            children = [None] * 5
            children[0] = perm[0]
            children[1] = "Fred"   # Clue 3
            children[2] = "Bella"  # Clue 7: Fred is directly left of Bella.
            children[3] = perm[1]
            children[4] = perm[2]
            
            # Verify that Samantha appears in the children list.
            if "Samantha" not in children:
                continue
            # Determine the house number (1-indexed) where the child is Samantha.
            index_samantha = children.index("Samantha")
            house_samantha = index_samantha + 1

            # Clue 1: Bob is somewhere to the left of the house whose child is Samantha.
            house_bob = parent_perm.index("Bob") + 1
            if house_bob >= house_samantha:
                continue

            # Clue 2: The house with child Timothy is somewhere to the left of the house with child Samantha.
            if "Timothy" not in children:
                continue
            house_timothy = children.index("Timothy") + 1
            if house_timothy >= house_samantha:
                continue

            # Clue 4: There is one house between Alice and the house with child Samantha.
            house_alice = parent_perm.index("Alice") + 1
            if abs(house_alice - house_samantha) != 2:
                continue

            # Clue 8: The house with child Samantha is somewhere to the left of the house where Peter lives.
            house_peter = parent_perm.index("Peter") + 1
            if house_samantha >= house_peter:
                continue

            # If all constraints are satisfied, we have found the solution.
            solution = {
                "solution": {
                    "header": ["House", "Name", "Children"],
                    "rows": [
                        ["1", parent_perm[0], children[0]],
                        ["2", parent_perm[1], children[1]],
                        ["3", parent_perm[2], children[2]],
                        ["4", parent_perm[3], children[3]],
                        ["5", parent_perm[4], children[4]]
                    ]
                }
            }
            print(json.dumps(solution, indent=2))
            return

if __name__ == "__main__":
    main()