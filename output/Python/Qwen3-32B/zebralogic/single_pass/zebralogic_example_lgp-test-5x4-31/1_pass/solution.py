import itertools
import json

def main():
    # Define the possible categories
    names = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
    vacations = ['cruise', 'city', 'camping', 'beach', 'mountain']
    children = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy']
    nationalities = ['dane', 'norwegian', 'brit', 'german', 'swede']

    # Generate filtered permutations
    vac_perm = [p for p in itertools.permutations(vacations) if p[0] == 'cruise']
    nat_perm = [p for p in itertools.permutations(nationalities) if p[4] == 'dane']
    child_perm = [p for p in itertools.permutations(children) if p[3] == 'Meredith']
    names_perm = list(itertools.permutations(names))

    # Iterate through all combinations
    for names_p in names_perm:
        for vac_p in vac_perm:
            for child_p in child_perm:
                for nat_p in nat_perm:
                    # Check if valid
                    # Clue 1: Norwegian is Peter
                    norwegian_idx = nat_p.index('norwegian')
                    if names_p[norwegian_idx] != 'Peter':
                        continue

                    # Clue 5: Brit is Alice
                    brit_idx = nat_p.index('brit')
                    if names_p[brit_idx] != 'Alice':
                        continue

                    # Clue 2: Swede's child is Bella
                    swede_idx = nat_p.index('swede')
                    if child_p[swede_idx] != 'Bella':
                        continue

                    # Clue 3: Beach vacation directly left of Samantha's house
                    beach_idx = vac_p.index('beach')
                    if beach_idx == 4:
                        continue
                    if child_p[beach_idx + 1] != 'Samantha':
                        continue

                    # Clue 4: child Bella not in house 2 (index 1)
                    if child_p[1] == 'Bella':
                        continue

                    # Clue 8: Eric not in house 5 (index 4)
                    if names_p[4] == 'Eric':
                        continue

                    # Clue 9: Swede to the right of Norwegian
                    if swede_idx <= norwegian_idx:
                        continue

                    # Clue 10: One house between Fred and city
                    fred_idx = None
                    for i, c in enumerate(child_p):
                        if c == 'Fred':
                            fred_idx = i
                            break
                    city_idx = vac_p.index('city')
                    if abs(fred_idx - city_idx) != 2:
                        continue

                    # Clue 11: Bob is camping
                    camping_idx = vac_p.index('camping')
                    if names_p[camping_idx] != 'Bob':
                        continue

                    # Clue 13: camping not in fifth house (index 4)
                    if camping_idx == 4:
                        continue

                    # If passed all checks
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                            "rows": []
                        }
                    }
                    for i in range(5):
                        house_num = str(i + 1)
                        solution["solution"]["rows"].append([
                            house_num,
                            names_p[i],
                            vac_p[i],
                            child_p[i],
                            nat_p[i]
                        ])
                    # Output as JSON
                    print(json.dumps(solution))
                    return

    # If no solution found (should not happen)
    print(json.dumps({"solution": {"header": [], "rows": []}}))

if __name__ == "__main__":
    main()