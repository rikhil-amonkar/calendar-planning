import itertools
import json

def solve_puzzle():
    names = ['Peter', 'Arnold', 'Eric', 'Alice']
    flowers = ['daffodils', 'carnations', 'roses', 'lilies']
    heights = ['very short', 'short', 'tall', 'average']
    mothers = ['Janelle', 'Kailyn', 'Holly', 'Aniya']
    occupations = ['engineer', 'doctor', 'teacher', 'artist']
    sports = ['swimming', 'basketball', 'tennis', 'soccer']

    for name_perm in itertools.permutations(names):
        # Clue 9: Arnold is not in the third house
        if name_perm[2] == 'Arnold':
            continue

        arnold_pos = name_perm.index('Arnold')
        eric_pos = name_perm.index('Eric')
        peter_pos = name_perm.index('Peter')
        alice_pos = name_perm.index('Alice')

        for flower_perm in itertools.permutations(flowers):
            # Clue 2: Eric loves roses
            if flower_perm[eric_pos] != 'roses':
                continue
            # Clue 13: Arnold loves lilies
            if flower_perm[arnold_pos] != 'lilies':
                continue

            for height_perm in itertools.permutations(heights):
                # Clue 3: Arnold is tall
                if height_perm[arnold_pos] != 'tall':
                    continue

                for mother_perm in itertools.permutations(mothers):
                    # Clue 12: Alice's mother is Aniya
                    if mother_perm[alice_pos] != 'Aniya':
                        continue
                    # Clue 7: Janelle's mother loves carnations
                    janelle_valid = True
                    for i in range(4):
                        if mother_perm[i] == 'Janelle':
                            if flower_perm[i] != 'carnations':
                                janelle_valid = False
                                break
                    if not janelle_valid:
                        continue

                    for occupation_perm in itertools.permutations(occupations):
                        # Clue 6: Teacher is in the first house
                        if occupation_perm[0] != 'teacher':
                            continue
                        # Clue 11: Peter is a doctor
                        if occupation_perm[peter_pos] != 'doctor':
                            continue

                        for sport_perm in itertools.permutations(sports):
                            # Clue 1: Swimming is with roses (Eric's sport is swimming)
                            if sport_perm[eric_pos] != 'swimming':
                                continue
                            # Clue 5: Soccer is short
                            soccer_pos = sport_perm.index('soccer')
                            if height_perm[soccer_pos] != 'short':
                                continue
                            # Clue 8: Basketball is average
                            basketball_pos = sport_perm.index('basketball')
                            if height_perm[basketball_pos] != 'average':
                                continue

                            # Clue 10: Holly's mother is to the right of average height
                            holly_mother_pos = -1
                            for i in range(4):
                                if mother_perm[i] == 'Holly':
                                    holly_mother_pos = i
                                    break
                            if holly_mother_pos == -1:
                                continue
                            average_height_pos = height_perm.index('average')
                            if holly_mother_pos <= average_height_pos:
                                continue

                            # Clue 4: Daffodils is to the right of engineer
                            daffodils_pos = flower_perm.index('daffodils')
                            engineer_pos = occupation_perm.index('engineer')
                            if daffodils_pos <= engineer_pos:
                                continue

                            # All constraints satisfied, construct solution
                            solution = []
                            for i in range(4):
                                solution.append([
                                    str(i + 1),
                                    name_perm[i],
                                    flower_perm[i],
                                    height_perm[i],
                                    mother_perm[i],
                                    occupation_perm[i],
                                    sport_perm[i]
                                ])
                            return json.dumps({
                                "solution": {
                                    "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                                    "rows": solution
                                }
                            })

    return json.dumps({"solution": {"header": [], "rows": []}})

if __name__ == "__main__":
    print(solve_puzzle())