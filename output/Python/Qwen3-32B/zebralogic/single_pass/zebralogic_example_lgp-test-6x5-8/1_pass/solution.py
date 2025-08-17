import json

def solve_puzzle():
    names = ['Arnold', 'Peter', 'Bob', 'Eric', 'Carol', 'Alice']
    animals = ['horse', 'rabbit', 'fish', 'cat', 'bird', 'dog']
    occupations = ['engineer', 'nurse', 'lawyer', 'teacher', 'artist', 'doctor']
    sports = ['basketball', 'volleyball', 'soccer', 'tennis', 'baseball', 'swimming']
    heights = ['average', 'tall', 'short', 'very short', 'very tall', 'super tall']

    def backtrack(house_idx, houses, used_names, used_animals, used_occupations, used_sports, used_heights):
        if house_idx == 6:
            return check_remaining_constraints(houses)
        current_house_num = house_idx + 1

        required_sport = None
        required_occupation = None
        required_animal = None
        required_height = None

        if current_house_num == 1:
            required_sport = 'baseball'
        elif current_house_num == 2:
            required_occupation = 'engineer'
            required_animal = 'dog'
        elif current_house_num == 5:
            required_occupation = 'lawyer'
            required_height = 'super tall'

        possible_names = [n for n in names if n not in used_names]
        for name in possible_names:
            conflict = False
            if name == 'Carol' and current_house_num == 1:
                conflict = True
            elif name == 'Peter' and current_house_num == 2:
                conflict = True
            if conflict:
                continue

            new_used_names = used_names.copy()
            new_used_names.add(name)

            possible_animals = [a for a in animals if a not in used_animals]
            if name == 'Arnold':
                if 'cat' not in possible_animals:
                    continue
                possible_animals = ['cat']
            elif name == 'Carol':
                if 'fish' not in possible_animals:
                    continue
                possible_animals = ['fish']
            elif name == 'Alice':
                if 'rabbit' not in possible_animals:
                    continue
                possible_animals = ['rabbit']
            if required_animal:
                if required_animal not in possible_animals:
                    continue
                possible_animals = [required_animal]

            for animal in possible_animals:
                new_used_animals = used_animals.copy()
                new_used_animals.add(animal)

                possible_occupations = [o for o in occupations if o not in used_occupations]
                if name == 'Peter':
                    if 'nurse' not in possible_occupations:
                        continue
                    possible_occupations = ['nurse']
                if animal == 'horse':
                    if 'teacher' not in possible_occupations:
                        continue
                    possible_occupations = ['teacher']
                if required_occupation:
                    if required_occupation not in possible_occupations:
                        continue
                    possible_occupations = [required_occupation]

                for occupation in possible_occupations:
                    new_used_occupations = used_occupations.copy()
                    new_used_occupations.add(occupation)

                    possible_sports = [s for s in sports if s not in used_sports]
                    if name == 'Carol':
                        if 'soccer' not in possible_sports:
                            continue
                        possible_sports = ['soccer']
                    if required_sport:
                        if required_sport not in possible_sports:
                            continue
                        possible_sports = [required_sport]
                    if occupation == 'teacher':
                        if 'tennis' not in possible_sports:
                            continue
                        possible_sports = ['tennis']

                    for sport in possible_sports:
                        new_used_sports = used_sports.copy()
                        new_used_sports.add(sport)

                        possible_heights = [h for h in heights if h not in used_heights]
                        if sport == 'volleyball':
                            if 'tall' not in possible_heights:
                                continue
                            possible_heights = ['tall']
                        elif sport != 'volleyball':
                            possible_heights = [h for h in possible_heights if h != 'tall']
                        if sport == 'swimming':
                            if 'average' not in possible_heights:
                                continue
                            possible_heights = ['average']
                        elif sport != 'swimming':
                            possible_heights = [h for h in possible_heights if h != 'average']
                        if required_height:
                            if required_height not in possible_heights:
                                continue
                            possible_heights = [required_height]

                        for height in possible_heights:
                            new_used_heights = used_heights.copy()
                            new_used_heights.add(height)

                            new_houses = houses.copy()
                            new_houses.append({
                                'name': name,
                                'animal': animal,
                                'occupation': occupation,
                                'sport': sport,
                                'height': height
                            })

                            result = backtrack(
                                house_idx + 1,
                                new_houses,
                                new_used_names,
                                new_used_animals,
                                new_used_occupations,
                                new_used_sports,
                                new_used_heights
                            )
                            if result is not None:
                                return result

                            new_houses.pop()

                        new_used_heights.discard(height)
                    new_used_sports.discard(sport)
                new_used_occupations.discard(occupation)
            new_used_animals.discard(animal)
        new_used_names.discard(name)
        return None

    def check_remaining_constraints(houses):
        average_height_index = None
        short_index = None
        tall_index = None
        very_short_index = None
        rabbit_index = None
        teacher_index = None
        soccer_index = None
        artist_index = None
        arnold_index = None

        for i, house in enumerate(houses):
            if house['height'] == 'average':
                average_height_index = i
            if house['height'] == 'short':
                short_index = i
            if house['height'] == 'tall':
                tall_index = i
            if house['height'] == 'very short':
                very_short_index = i
            if house['animal'] == 'rabbit':
                rabbit_index = i
            if house['occupation'] == 'teacher':
                teacher_index = i
            if house['sport'] == 'soccer':
                soccer_index = i
            if house['occupation'] == 'artist':
                artist_index = i
            if house['name'] == 'Arnold':
                arnold_index = i

        if average_height_index is None or short_index is None or not (average_height_index < short_index):
            return None
        if average_height_index is None or rabbit_index is None or not (average_height_index + 1 == rabbit_index):
            return None
        if tall_index is None or very_short_index is None or not (tall_index < very_short_index):
            return None
        if teacher_index is None or soccer_index is None or not (teacher_index + 1 == soccer_index):
            return None

        bob_index = None
        for i, house in enumerate(houses):
            if house['name'] == 'Bob':
                bob_index = i
        if artist_index is None or bob_index is None or not (artist_index < bob_index):
            return None
        if very_short_index is None or arnold_index is None or not (very_short_index < arnold_index):
            return None

        return houses

    solution = backtrack(0, [], set(), set(), set(), set(), set())
    return solution

solution_data = solve_puzzle()
if solution_data:
    header = ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"]
    rows = []
    for i in range(6):
        house_num = i + 1
        row = [
            str(house_num),
            solution_data[i]['name'],
            solution_data[i]['animal'],
            solution_data[i]['occupation'],
            solution_data[i]['sport'],
            solution_data[i]['height']
        ]
        rows.append(row)
    json_output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(json_output, indent=2))
else:
    print(json.dumps({"solution": {"header": [], "rows": []}}))