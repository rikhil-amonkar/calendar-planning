import json

def is_valid_solution(houses):
    # Check if all constraints are satisfied
    constraints = [
        lambda h: h[h.index(next(x for x in h if x['Children'] == 'Meredith'))]['Height'] == 'average',
        lambda h: h[1]['Height'] == 'tall',
        lambda h: h.index(next(x for x in h if x['HouseStyle'] == 'victorian')) - h.index(next(x for x in h if x['Name'] == 'Peter')) == 1,
        lambda h: next(x for x in h if x['Name'] == 'Alice')['Height'] == 'tall',
        lambda h: next(x for x in h if x['FavoriteSport'] == 'baseball')['Height'] == 'very tall',
        lambda h: abs(h.index(next(x for x in h if x['Children'] == 'Meredith')) - h.index(next(x for x in h if x['Children'] == 'Timothy'))) == 1,
        lambda h: next(x for x in h if x['Name'] == 'Bob')['Hobby'] == 'painting',
        lambda h: h[1]['Hobby'] == 'gardening',
        lambda h: h.index(next(x for x in h if x['Name'] == 'Eric')) < h.index(next(x for x in h if x['Height'] == 'very short')),
        lambda h: next(x for x in h if x['FavoriteSport'] == 'tennis')['Children'] == 'Samantha',
        lambda h: h[0]['FavoriteSport'] != 'soccer',
        lambda h: next(x for x in h if x['Children'] == 'Samantha')['HouseStyle'] == 'modern',
        lambda h: next(x for x in h if x['HouseStyle'] == 'craftsman')['Height'] == 'average',
        lambda h: next(x for x in h if x['Children'] == 'Fred')['HouseStyle'] == 'victorian',
        lambda h: next(x for x in h if x['FavoriteSport'] == 'basketball')['Height'] == 'short',
        lambda h: next(x for x in h if x['Name'] == 'Peter')['Height'] == 'very tall',
        lambda h: h.index(next(x for x in h if x['HouseStyle'] == 'ranch')) < h.index(next(x for x in h if x['Hobby'] == 'cooking')),
        lambda h: abs(h.index(next(x for x in h if x['Hobby'] == 'knitting')) - h.index(next(x for x in h if x['Hobby'] == 'gardening'))) == 1,
        lambda h: next(x for x in h if x['HouseStyle'] == 'modern')['Hobby'] == 'cooking',
        lambda h: next(x for x in h if x['HouseStyle'] == 'victorian'])['House'] == '5'
    ]

    return all(constraint(houses) for constraint in constraints)

def solve_puzzle():
    # Initialize houses with all possible values
    houses = [
        {'House': str(i+1), 'Name': ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric'],
         'Hobby': ['cooking', 'gardening', 'painting', 'photography', 'knitting'],
         'FavoriteSport': ['swimming', 'tennis', 'soccer', 'baseball', 'basketball'],
         'HouseStyle': ['ranch', 'craftsman', 'victorian', 'modern', 'colonial'],
         'Children': ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred'],
         'Height': ['average', 'very tall', 'very short', 'short', 'tall']}
        for i in range(5)
    ]

    def backtrack(index):
        if index == 5:
            if is_valid_solution(houses):
                return True
            return False

        for name in houses[index]['Name']:
            if any(h['Name'] == name for h in houses[:index]):
                continue
            houses[index]['Name'] = [name]

            for hobby in houses[index]['Hobby']:
                if any(h['Hobby'] == hobby for h in houses[:index]):
                    continue
                houses[index]['Hobby'] = [hobby]

                for sport in houses[index]['FavoriteSport']:
                    if any(h['FavoriteSport'] == sport for h in houses[:index]):
                        continue
                    houses[index]['FavoriteSport'] = [sport]

                    for style in houses[index]['HouseStyle']:
                        if any(h['HouseStyle'] == style for h in houses[:index]):
                            continue
                        houses[index]['HouseStyle'] = [style]

                        for child in houses[index]['Children']:
                            if any(h['Children'] == child for h in houses[:index]):
                                continue
                            houses[index]['Children'] = [child]

                            for height in houses[index]['Height']:
                                if any(h['Height'] == height for h in houses[:index]):
                                    continue
                                houses[index]['Height'] = [height]

                                if backtrack(index + 1):
                                    return True

        return False

    if backtrack(0):
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
                "rows": [[h['House'], h['Name'][0], h['Hobby'][0], h['FavoriteSport'][0], h['HouseStyle'][0], h['Children'][0], h['Height'][0]] for h in houses]
            }
        }
        return json.dumps(solution, indent=2)
    else:
        return "No solution found"

print(solve_puzzle())