import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Peter', 'Eric', 'Bob', 'Arnold', 'Carol']
    cigars = ['pall mall', 'yellow monster', 'dunhill', 'blue master', 'prince', 'blends']
    music_genres = ['hip hop', 'jazz', 'country', 'pop', 'classical', 'rock']
    drinks = ['water', 'milk', 'boba tea', 'tea', 'root beer', 'coffee']
    mothers = ['Kailyn', 'Penny', 'Janelle', 'Holly', 'Sarah', 'Aniya']
    foods = ['soup', 'pizza', 'spaghetti', 'stir fry', 'stew', 'grilled cheese']

    # Generate all possible permutations for each attribute
    for name_perm in itertools.permutations(names):
        for cigar_perm in itertools.permutations(cigars):
            for music_perm in itertools.permutations(music_genres):
                for drink_perm in itertools.permutations(drinks):
                    for mother_perm in itertools.permutations(mothers):
                        for food_perm in itertools.permutations(foods):
                            # Create a dictionary to hold the current assignment
                            assignment = {}
                            for i in range(6):
                                assignment[i+1] = {
                                    'Name': name_perm[i],
                                    'Cigar': cigar_perm[i],
                                    'MusicGenre': music_perm[i],
                                    'Drink': drink_perm[i],
                                    'Mother': mother_perm[i],
                                    'Food': food_perm[i]
                                }

                            # Check all constraints
                            valid = True

                            # Clue 2: Eric is not in the second house.
                            if assignment[2]['Name'] == 'Eric':
                                valid = False

                            # Clue 5: Eric is directly left of Carol.
                            carol_pos = None
                            eric_pos = None
                            for pos in range(1, 6):
                                if assignment[pos]['Name'] == 'Eric':
                                    eric_pos = pos
                                if assignment[pos]['Name'] == 'Carol':
                                    carol_pos = pos
                            if eric_pos is None or carol_pos is None or carol_pos != eric_pos + 1:
                                valid = False

                            # Clue 1: Carol is directly left of the person who loves eating grilled cheese.
                            if carol_pos is not None:
                                if carol_pos == 6 or assignment[carol_pos + 1]['Food'] != 'grilled cheese':
                                    valid = False

                            # Clue 3: The person whose mother's name is Holly is somewhere to the right of Carol.
                            if carol_pos is not None:
                                holly_pos = None
                                for pos in range(1, 7):
                                    if assignment[pos]['Mother'] == 'Holly':
                                        holly_pos = pos
                                        break
                                if holly_pos is None or holly_pos <= carol_pos:
                                    valid = False

                            # Clue 4: The person who loves grilled cheese is right of the person who loves rock.
                            grilled_cheese_pos = None
                            rock_pos = None
                            for pos in range(1, 7):
                                if assignment[pos]['Food'] == 'grilled cheese':
                                    grilled_cheese_pos = pos
                                if assignment[pos]['MusicGenre'] == 'rock':
                                    rock_pos = pos
                            if grilled_cheese_pos is None or rock_pos is None or grilled_cheese_pos <= rock_pos:
                                valid = False

                            # Clue 6: pop music is not in the third house.
                            if assignment[3]['MusicGenre'] == 'pop':
                                valid = False

                            # Clue 7: Eric loves country music.
                            if eric_pos is not None and assignment[eric_pos]['MusicGenre'] != 'country':
                                valid = False

                            # Clue 8: classical music is in the sixth house.
                            if assignment[6]['MusicGenre'] != 'classical':
                                valid = False

                            # Clue 9: coffee drinker is Bob.
                            bob_pos = None
                            for pos in range(1, 7):
                                if assignment[pos]['Name'] == 'Bob':
                                    bob_pos = pos
                            if bob_pos is None or assignment[bob_pos]['Drink'] != 'coffee':
                                valid = False

                            # Clue 10: blends smoker is Peter.
                            peter_pos = None
                            for pos in range(1, 7):
                                if assignment[pos]['Name'] == 'Peter':
                                    peter_pos = pos
                            if peter_pos is None or assignment[peter_pos]['Cigar'] != 'blends':
                                valid = False

                            # Clue 11: stew is not in the fifth house.
                            if assignment[5]['Food'] == 'stew':
                                valid = False

                            # Clue 12: root beer lover is directly left of Janelle's mother.
                            root_beer_pos = None
                            janelle_pos = None
                            for pos in range(1, 6):
                                if assignment[pos]['Drink'] == 'root beer':
                                    root_beer_pos = pos
                                if assignment[pos]['Mother'] == 'Janelle':
                                    janelle_pos = pos
                            if root_beer_pos is None or janelle_pos is None or janelle_pos != root_beer_pos + 1:
                                valid = False

                            # Clue 13: two houses between Sarah's mother and yellow monster smoker.
                            sarah_pos = None
                            yellow_monster_pos = None
                            for pos in range(1, 7):
                                if assignment[pos]['Mother'] == 'Sarah':
                                    sarah_pos = pos
                                if assignment[pos]['Cigar'] == 'yellow monster':
                                    yellow_monster_pos = pos
                            if sarah_pos is None or yellow_monster_pos is None or yellow_monster_pos - sarah_pos != 3:
                                valid = False

                            # Clue 14: Eric is the tea drinker.
                            if eric_pos is not None and assignment[eric_pos]['Drink'] != 'tea':
                                valid = False

                            # Clue 15: pall mall is right of stir fry.
                            pall_mall_pos = None
                            stir_fry_pos = None
                            for pos in range(1, 7):
                                if assignment[pos]['Cigar'] == 'pall mall':
                                    pall_mall_pos = pos
                                if assignment[pos]['Food'] == 'stir fry':
                                    stir_fry_pos = pos
                            if pall_mall_pos is not None and stir_fry_pos is not None and pall_mall_pos <= stir_fry_pos:
                                valid = False

                            # Clue 16: soup lover is Bob.
                            if bob_pos is not None and assignment[bob_pos]['Food'] != 'soup':
                                valid = False

                            # Clue 17: hip hop is directly left of Kailyn's mother.
                            hip_hop_pos = None
                            kailyn_pos = None
                            for pos in range(1, 6):
                                if assignment[pos]['MusicGenre'] == 'hip hop':
                                    hip_hop_pos = pos
                                if assignment[pos]['Mother'] == 'Kailyn':
                                    kailyn_pos = pos
                            if hip_hop_pos is None or kailyn_pos is None or kailyn_pos != hip_hop_pos + 1:
                                valid = False

                            # Clue 18: Arnold is right of Kailyn's mother.
                            if kailyn_pos is not None:
                                arnold_pos = None
                                for pos in range(1, 7):
                                    if assignment[pos]['Name'] == 'Arnold':
                                        arnold_pos = pos
                                if arnold_pos is None or arnold_pos <= kailyn_pos:
                                    valid = False

                            # Clue 19: water drinker is directly left of blue master smoker.
                            water_pos = None
                            blue_master_pos = None
                            for pos in range(1, 6):
                                if assignment[pos]['Drink'] == 'water':
                                    water_pos = pos
                                if assignment[pos]['Cigar'] == 'blue master':
                                    blue_master_pos = pos
                            if water_pos is None or blue_master_pos is None or blue_master_pos != water_pos + 1:
                                valid = False

                            # Clue 20: spaghetti is left of blends smoker.
                            spaghetti_pos = None
                            blends_pos = None
                            for pos in range(1, 7):
                                if assignment[pos]['Food'] == 'spaghetti':
                                    spaghetti_pos = pos
                                if assignment[pos]['Cigar'] == 'blends':
                                    blends_pos = pos
                            if spaghetti_pos is not None and blends_pos is not None and spaghetti_pos >= blends_pos:
                                valid = False

                            # Clue 21: Sarah's mother is directly left of jazz lover.
                            if sarah_pos is not None:
                                jazz_pos = None
                                for pos in range(1, 7):
                                    if assignment[pos]['MusicGenre'] == 'jazz':
                                        jazz_pos = pos
                                if jazz_pos is None or jazz_pos != sarah_pos + 1:
                                    valid = False

                            # Clue 22: hip hop is directly left of root beer lover.
                            if hip_hop_pos is not None and root_beer_pos is not None and root_beer_pos != hip_hop_pos + 1:
                                valid = False

                            # Clue 23: water drinker loves stew.
                            if water_pos is not None and assignment[water_pos]['Food'] != 'stew':
                                valid = False

                            # Clue 24: dunhill is not in the second house.
                            if assignment[2]['Cigar'] == 'dunhill':
                                valid = False

                            # Clue 25: milk drinker is Janelle's mother.
                            if janelle_pos is not None and assignment[janelle_pos]['Drink'] != 'milk':
                                valid = False

                            # Clue 26: Eric's mother is Aniya.
                            if eric_pos is not None and assignment[eric_pos]['Mother'] != 'Aniya':
                                valid = False

                            if valid:
                                # Prepare the solution in the required JSON format
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
                                        "rows": []
                                    }
                                }
                                for house in range(1, 7):
                                    row = [
                                        str(house),
                                        assignment[house]['Name'],
                                        assignment[house]['Cigar'],
                                        assignment[house]['MusicGenre'],
                                        assignment[house]['Drink'],
                                        assignment[house]['Mother'],
                                        assignment[house]['Food']
                                    ]
                                    solution["solution"]["rows"].append(row)
                                return json.dumps(solution, indent=2)

    return json.dumps({"solution": {"header": [], "rows": []}})

if __name__ == "__main__":
    print(solve_puzzle())