import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
    vacations = ['cruise', 'city', 'camping', 'beach', 'mountain']
    children = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy']
    nationalities = ['dane', 'norwegian', 'brit', 'german', 'swede']

    for name_order in itertools.permutations(names):
        for vacation_order in itertools.permutations(vacations):
            for children_order in itertools.permutations(children):
                for nationality_order in itertools.permutations(nationalities):
                    # Create a list of dictionaries for each house
                    houses_info = [
                        {'house': houses[i], 'name': name_order[i], 'vacation': vacation_order[i],
                         'children': children_order[i], 'nationality': nationality_order[i]}
                        for i in range(5)
                    ]

                    # Apply constraints
                    if (houses_info[0]['nationality'] == 'norwegian' and houses_info[0]['name'] == 'Peter' and
                        houses_info[houses_info.index(next(house for house in houses_info if house['children'] == 'Bella'))]['nationality'] == 'swede' and
                        houses_info.index(next(house for house in houses_info if house['vacation'] == 'beach')) + 1 == houses_info.index(next(house for house in houses_info if house['children'] == 'Samantha')) and
                        houses_info[houses_info.index(next(house for house in houses_info if house['children'] == 'Bella'))]['house'] != 2 and
                        houses_info[houses_info.index(next(house for house in houses_info if house['name'] == 'Alice'))]['nationality'] == 'brit' and
                        houses_info[0]['vacation'] == 'cruise' and
                        houses_info[3]['children'] == 'Meredith' and
                        houses_info[4]['nationality'] == 'dane' and
                        houses_info[houses_info.index(next(house for house in houses_info if house['name'] == 'Eric'))]['house'] != 5 and
                        houses_info.index(next(house for house in houses_info if house['nationality'] == 'swede')) > houses_info.index(next(house for house in houses_info if house['nationality'] == 'norwegian')) and
                        abs(houses_info.index(next(house for house in houses_info if house['children'] == 'Fred')) - houses_info.index(next(house for house in houses_info if house['vacation'] == 'city'))) == 1 and
                        houses_info[houses_info.index(next(house for house in houses_info if house['name'] == 'Bob'))]['vacation'] == 'camping' and
                        houses_info[houses_info.index(next(house for house in houses_info if house['vacation'] == 'camping'))]['house'] != 5):

                        # If all constraints are satisfied, return the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                                "rows": [
                                    [str(house['house']), house['name'], house['vacation'], house['children'], house['nationality']]
                                    for house in houses_info
                                ]
                            }
                        }
                        return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())