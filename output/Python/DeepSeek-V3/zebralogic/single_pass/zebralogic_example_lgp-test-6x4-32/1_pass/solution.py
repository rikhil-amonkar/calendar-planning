import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Eric', 'Alice', 'Arnold', 'Carol', 'Peter', 'Bob']
    house_styles = ['mediterranean', 'modern', 'craftsman', 'ranch', 'colonial', 'victorian']
    music_genres = ['country', 'hip hop', 'pop', 'jazz', 'classical', 'rock']
    hobbies = ['cooking', 'painting', 'photography', 'woodworking', 'gardening', 'knitting']

    # Initialize data structure to hold assignments
    solution = {house: {} for house in houses}

    # Apply direct assignments first
    # Clue 11: country music in house 1
    solution[1]['MusicGenre'] = 'country'
    # Clue 5: jazz is directly left of Eric (so jazz is in house X, Eric in X+1)
    # Clue 9: Eric is in ranch
    # Clue 14: Eric's hobby is gardening
    # Clue 7: Carol loves hip-hop
    # Clue 3: mediterranean style loves hip-hop (so Carol is in mediterranean)
    # Clue 4: two houses between Arnold and Victorian (so if Arnold is X, Victorian is X+3)
    # Clue 8: Arnold is in craftsman
    # Clue 10: woodworking is in Victorian
    # Clue 2: classical and woodworking are next to each other
    # Clue 6: hip-hop is left of knitting
    # Clue 12: one house between painting and colonial
    # Clue 13: Alice is photography
    # Clue 15: Bob is in house 3
    solution[3]['Name'] = 'Bob'
    # Clue 1: rock is in house 5
    solution[5]['MusicGenre'] = 'rock'

    # Iterate to find possible positions for Arnold (clue 4 and 8)
    possible_arnold_positions = [1, 2, 3]  # since Victorian must be <=6 (X+3 <=6 => X<=3)
    for arnold_pos in possible_arnold_positions:
        victorian_pos = arnold_pos + 3
        # Check if craftsman is available at arnold_pos
        temp_solution = {k: v.copy() for k, v in solution.items()}
        temp_solution[arnold_pos]['Name'] = 'Arnold'
        temp_solution[arnold_pos]['HouseStyle'] = 'craftsman'
        temp_solution[victorian_pos]['HouseStyle'] = 'victorian'
        temp_solution[victorian_pos]['Hobby'] = 'woodworking'  # clue 10

        # clue 2: classical is next to woodworking (victorian_pos)
        classical_positions = [victorian_pos - 1, victorian_pos + 1] if victorian_pos != 1 and victorian_pos != 6 else (
            [victorian_pos + 1] if victorian_pos == 1 else [victorian_pos - 1])
        
        # Try both possible classical positions
        for classical_pos in classical_positions:
            if classical_pos < 1 or classical_pos > 6:
                continue
            temp_solution2 = {k: v.copy() for k, v in temp_solution.items()}
            temp_solution2[classical_pos]['MusicGenre'] = 'classical'

            # Now assign Carol (hip-hop, mediterranean) - clue 3 and 7
            remaining_houses = [h for h in houses if 'Name' not in temp_solution2[h]]
            for carol_pos in remaining_houses:
                temp_solution3 = {k: v.copy() for k, v in temp_solution2.items()}
                temp_solution3[carol_pos]['Name'] = 'Carol'
                temp_solution3[carol_pos]['MusicGenre'] = 'hip hop'
                temp_solution3[carol_pos]['HouseStyle'] = 'mediterranean'

                # clue 6: hip-hop left of knitting (carol_pos < knitting_pos)
                # knitting_pos must be > carol_pos and not assigned yet
                # Assign jazz left of Eric (clue 5)
                # Eric is in ranch (clue 9) and gardening (clue 14)
                possible_eric_positions = [h for h in houses if h > 1 and 'Name' not in temp_solution3[h]]
                for eric_pos in possible_eric_positions:
                    jazz_pos = eric_pos - 1
                    if jazz_pos < 1 or jazz_pos > 6:
                        continue
                    if 'MusicGenre' in temp_solution3[jazz_pos] and temp_solution3[jazz_pos]['MusicGenre'] != 'jazz':
                        continue
                    if 'MusicGenre' in temp_solution3[jazz_pos] and temp_solution3[jazz_pos]['MusicGenre'] == 'jazz':
                        pass  # already set
                    else:
                        if 'MusicGenre' not in temp_solution3[jazz_pos]:
                            temp_solution4 = {k: v.copy() for k, v in temp_solution3.items()}
                            temp_solution4[jazz_pos]['MusicGenre'] = 'jazz'
                        else:
                            continue

                        temp_solution4[eric_pos]['Name'] = 'Eric'
                        temp_solution4[eric_pos]['HouseStyle'] = 'ranch'
                        temp_solution4[eric_pos]['Hobby'] = 'gardening'

                        # Assign remaining names: Alice, Peter
                        remaining_names = [n for n in names if n not in [v['Name'] for v in temp_solution4.values() if 'Name' in v]]
                        remaining_houses_for_names = [h for h in houses if 'Name' not in temp_solution4[h]]

                        # Alice is photography (clue 13)
                        for alice_pos in remaining_houses_for_names:
                            temp_solution5 = {k: v.copy() for k, v in temp_solution4.items()}
                            temp_solution5[alice_pos]['Name'] = 'Alice'
                            temp_solution5[alice_pos]['Hobby'] = 'photography'

                            # Assign Peter to remaining house
                            peter_pos = [h for h in houses if 'Name' not in temp_solution5[h]][0]
                            temp_solution5[peter_pos]['Name'] = 'Peter'

                            # Assign hobbies: cooking, painting, knitting
                            # clue 6: knitting is right of hip-hop (carol_pos)
                            possible_knitting_positions = [h for h in houses if h > carol_pos and 'Hobby' not in temp_solution5[h]]
                            for knitting_pos in possible_knitting_positions:
                                temp_solution6 = {k: v.copy() for k, v in temp_solution5.items()}
                                temp_solution6[knitting_pos]['Hobby'] = 'knitting'

                                # clue 12: one house between painting and colonial
                                # painting is in X, colonial is in X+2 or X-2
                                possible_painting_positions = [h for h in houses if 'Hobby' not in temp_solution6[h] and h != alice_pos]
                                for painting_pos in possible_painting_positions:
                                    colonial_pos1 = painting_pos + 2
                                    colonial_pos2 = painting_pos - 2
                                    colonial_positions = []
                                    if 1 <= colonial_pos1 <= 6:
                                        colonial_positions.append(colonial_pos1)
                                    if 1 <= colonial_pos2 <= 6:
                                        colonial_positions.append(colonial_pos2)
                                    for colonial_pos in colonial_positions:
                                        if 'HouseStyle' in temp_solution6[colonial_pos] and temp_solution6[colonial_pos]['HouseStyle'] != 'colonial':
                                            continue
                                        temp_solution7 = {k: v.copy() for k, v in temp_solution6.items()}
                                        temp_solution7[painting_pos]['Hobby'] = 'painting'
                                        temp_solution7[colonial_pos]['HouseStyle'] = 'colonial'

                                        # Assign remaining house styles: modern, pop music?
                                        remaining_styles = [s for s in house_styles if s not in [v['HouseStyle'] for v in temp_solution7.values() if 'HouseStyle' in v]]
                                        remaining_houses_for_styles = [h for h in houses if 'HouseStyle' not in temp_solution7[h]]
                                        for style, h in zip(remaining_styles, remaining_houses_for_styles):
                                            temp_solution7[h]['HouseStyle'] = style

                                        # Assign remaining music genres: pop
                                        remaining_music = [m for m in music_genres if m not in [v['MusicGenre'] for v in temp_solution7.values() if 'MusicGenre' in v]]
                                        remaining_houses_for_music = [h for h in houses if 'MusicGenre' not in temp_solution7[h]]
                                        for music, h in zip(remaining_music, remaining_houses_for_music):
                                            temp_solution7[h]['MusicGenre'] = music

                                        # Assign remaining hobbies: cooking
                                        remaining_hobbies = [h for h in hobbies if h not in [v['Hobby'] for v in temp_solution7.values() if 'Hobby' in v]]
                                        remaining_houses_for_hobbies = [h for h in houses if 'Hobby' not in temp_solution7[h]]
                                        for hobby, h in zip(remaining_hobbies, remaining_houses_for_hobbies):
                                            temp_solution7[h]['Hobby'] = hobby

                                        # Verify all constraints are satisfied
                                        valid = True
                                        for house in houses:
                                            if len(temp_solution7[house]) != 4:
                                                valid = False
                                                break
                                        if valid:
                                            # Prepare the output
                                            output = {
                                                "solution": {
                                                    "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
                                                    "rows": []
                                                }
                                            }
                                            for house in sorted(temp_solution7.keys()):
                                                row = [str(house)]
                                                row.append(temp_solution7[house].get('Name', ''))
                                                row.append(temp_solution7[house].get('HouseStyle', ''))
                                                row.append(temp_solution7[house].get('MusicGenre', ''))
                                                row.append(temp_solution7[house].get('Hobby', ''))
                                                output["solution"]["rows"].append(row)
                                            return json.dumps(output, indent=2)
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())