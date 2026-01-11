import json

def is_valid(state):
    # Extract lists for easier access
    names = [house['Name'] for house in state]
    children = [house['Children'] for house in state]
    smoothies = [house['Smoothie'] for house in state]

    # Check constraints
    # 1. The person's child is named Fred and the Desert smoothie lover are next to each other.
    if 'Fred' in children and 'desert' in smoothies:
        idx_fred = children.index('Fred')
        idx_desert = smoothies.index('desert')
        if abs(idx_fred - idx_desert) != 1:
            return False

    # 2. The person who drinks Blueberry smoothies is somewhere to the left of the person's child is named Fred.
    if 'Fred' in children and 'blueberry' in smoothies:
        idx_fred = children.index('Fred')
        idx_blueberry = smoothies.index('blueberry')
        if idx_blueberry >= idx_fred:
            return False

    # 3. Alice is not in the fifth house.
    if names[4] == 'Alice':
        return False

    # 4. The person's child is named Samantha is not in the second house.
    if children[1] == 'Samantha':
        return False

    # 5. The Watermelon smoothie lover is somewhere to the right of the person who likes Cherry smoothies.
    if 'watermelon' in smoothies and 'cherry' in smoothies:
        idx_watermelon = smoothies.index('watermelon')
        idx_cherry = smoothies.index('cherry')
        if idx_watermelon <= idx_cherry:
            return False

    # 6. Alice is the person's child is named Alice.
    if 'Alice' in children:
        idx_alice_child = children.index('Alice')
        if names[idx_alice_child] != 'Alice':
            return False

    # 7. Alice is the Watermelon smoothie lover.
    if 'Alice' in names:
        idx_alice = names.index('Alice')
        if smoothies[idx_alice] != 'watermelon':
            return False

    # 8. Peter is somewhere to the right of the person's child is named Samantha.
    if 'Peter' in names and 'Samantha' in children:
        idx_peter = names.index('Peter')
        idx_samantha = children.index('Samantha')
        if idx_peter <= idx_samantha:
            return False

    # 9. Arnold is not in the second house.
    if names[1] == 'Arnold':
        return False

    # 10. Bob is the person who is the mother of Timothy.
    if 'Bob' in names:
        idx_bob = names.index('Bob')
        if children[idx_bob] != 'Timothy':
            return False

    # 11. Arnold is directly left of Carol.
    if 'Arnold' in names and 'Carol' in names:
        idx_arnold = names.index('Arnold')
        idx_carol = names.index('Carol')
        if idx_arnold + 1 != idx_carol:
            return False

    # 12. The person who likes Cherry smoothies is directly left of the person's child is named Samantha.
    if 'cherry' in smoothies and 'Samantha' in children:
        idx_cherry = smoothies.index('cherry')
        idx_samantha = children.index('Samantha')
        if idx_cherry + 1 != idx_samantha:
            return False

    # 13. The person's child is named Meredith is in the sixth house.
    if children[5] != 'Meredith':
        return False

    # 14. The Dragonfruit smoothie lover is the person's child is named Meredith.
    if 'dragonfruit' in smoothies:
        idx_dragonfruit = smoothies.index('dragonfruit')
        if children[idx_dragonfruit] != 'Meredith':
            return False

    return True

def solve(state, names_used, children_used, smoothies_used):
    if len(names_used) == 6:
        if is_valid(state):
            return state
        else:
            return None

    for i in range(6):
        if state[i]['Name'] is None:
            for name in ['Arnold', 'Peter', 'Carol', 'Alice', 'Bob', 'Eric']:
                if name not in names_used:
                    for child in ['Alice', 'Timothy', 'Bella', 'Meredith', 'Fred', 'Samantha']:
                        if child not in children_used:
                            for smoothie in ['desert', 'cherry', 'watermelon', 'blueberry', 'lime', 'dragonfruit']:
                                if smoothie not in smoothies_used:
                                    state[i]['Name'] = name
                                    state[i]['Children'] = child
                                    state[i]['Smoothie'] = smoothie
                                    result = solve(state, names_used | {name}, children_used | {child}, smoothies_used | {smoothie})
                                    if result:
                                        return result
                                    state[i]['Name'] = None
                                    state[i]['Children'] = None
                                    state[i]['Smoothie'] = None
    return None

def main():
    state = [{'Name': None, 'Children': None, 'Smoothie': None} for _ in range(6)]
    solution = solve(state, set(), set(), set())
    if solution:
        formatted_solution = {
            "solution": {
                "header": ["House", "Name", "Children", "Smoothie"],
                "rows": [[str(i+1), house['Name'], house['Children'], house['Smoothie']] for i, house in enumerate(solution)]
            }
        }
        print(json.dumps(formatted_solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()