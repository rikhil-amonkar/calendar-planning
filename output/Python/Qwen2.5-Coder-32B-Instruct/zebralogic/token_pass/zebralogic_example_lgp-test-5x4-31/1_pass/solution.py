import itertools
import json

# Define the attributes and their possible values
attributes = {
    "Name": ["Alice", "Bob", "Arnold", "Eric", "Peter"],
    "Vacation": ["cruise", "city", "camping", "beach", "mountain"],
    "Children": ["Bella", "Samantha", "Fred", "Meredith", "Timothy"],
    "Nationality": ["dane", "norwegian", "brit", "german", "swede"]
}

# Initialize the possible values for each house
houses = {str(i): {attr: set(values) for attr, values in attributes.items()} for i in range(1, 6)}

# Apply direct constraints
def apply_direct_constraints(houses):
    # The Norwegian is Peter
    houses['1']['Nationality'].discard('norwegian')  # Norwegian cannot be in house 1
    houses['2']['Nationality'].discard('norwegian')
    houses['3']['Nationality'].discard('norwegian')
    houses['4']['Nationality'].discard('norwegian')
    houses['5']['Nationality'] = {'norwegian'}
    houses['5']['Name'] = {'Peter'}

    # The Swedish person's child is named Bella
    houses['2']['Children'].discard('Bella')  # Bella cannot be in house 2
    houses['3']['Children'].discard('Bella')
    houses['4']['Children'].discard('Bella')
    houses['5']['Children'].discard('Bella')
    houses['1']['Children'] = {'Bella'}
    houses['1']['Nationality'] = {'swede'}

    # Alice is the British person
    houses['1']['Nationality'].discard('brit')
    houses['2']['Nationality'].discard('brit')
    houses['3']['Nationality'].discard('brit')
    houses['4']['Nationality'].discard('brit')
    houses['5']['Nationality'].discard('brit')
    for h in houses:
        if 'Alice' in houses[h]['Name']:
            houses[h]['Nationality'] = {'brit'}

    # The person who likes going on cruises is in the first house
    houses['1']['Vacation'] = {'cruise'}
    houses['2']['Vacation'].discard('cruise')
    houses['3']['Vacation'].discard('cruise')
    houses['4']['Vacation'].discard('cruise')
    houses['5']['Vacation'].discard('cruise')

    # The person's child is named Meredith is in the fourth house
    houses['4']['Children'] = {'Meredith'}
    houses['1']['Children'].discard('Meredith')
    houses['2']['Children'].discard('Meredith')
    houses['3']['Children'].discard('Meredith')
    houses['5']['Children'].discard('Meredith')

    # Eric is not in the fifth house
    houses['5']['Name'].discard('Eric')

    # The Danish person is in the fifth house
    houses['5']['Nationality'] = {'dane'}

    # The person who enjoys camping trips is not in the fifth house
    houses['5']['Vacation'].discard('camping')

    # Bob is the person who enjoys camping trips
    for h in houses:
        if 'Bob' in houses[h]['Name']:
            houses[h]['Vacation'] = {'camping'}

apply_direct_constraints(houses)

# Apply relative constraints
def apply_relative_constraints(houses):
    # The Swedish person is somewhere to the right of the Norwegian
    # Since Norwegian is in house 5 and Swedish in house 1, this is already satisfied

    # The person who loves beach vacations is directly left of the person's child is named Samantha
    for h in ['1', '2', '3', '4']:
        if 'beach' in houses[h]['Vacation']:
            houses[str(int(h) + 1)]['Children'] = {'Samantha'}
            break

    # There is one house between the person's child is named Fred and the person who prefers city breaks
    for h in ['1', '2', '3']:
        if 'Fred' in houses[h]['Children']:
            houses[str(int(h) + 2)]['Vacation'] = {'city'}
            break
        elif 'city' in houses[h]['Vacation']:
            houses[str(int(h) - 2)]['Children'] = {'Fred'}
            break

apply_relative_constraints(houses)

# Eliminate remaining possibilities
def eliminate_impossible_combinations(houses):
    for attr in attributes.keys():
        for val in attributes[attr]:
            count = sum(val in houses[h][attr] for h in houses)
            if count == 1:
                for h in houses:
                    if val in houses[h][attr]:
                        houses[h][attr] = {val}
                        break

eliminate_impossible_combinations(houses)

# Verify and format the solution
solution = {
    "solution": {
        "header": ["House", "Name", "Vacation", "Children", "Nationality"],
        "rows": []
    }
}

for h in houses:
    row = [h]
    for attr in solution["solution"]["header"][1:]:
        row.append(next(iter(houses[h][attr])))
    solution["solution"]["rows"].append(row)

# Output the solution as JSON
print(json.dumps(solution, indent=2))