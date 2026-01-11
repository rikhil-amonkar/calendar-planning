import json

def is_valid(state):
    # Unpack the state
    names, birthdays, foods, heights, car_models = state
    
    # Apply all constraints
    if car_models[4] != 'ford f150':
        return False
    if heights.index('short') != car_models.index('honda civic'):
        return False
    if foods.index('stir fry') >= foods.index('pizza'):
        return False
    if abs(foods.index('stir fry') - foods.index('pizza')) != 2:
        return False
    if foods.index('soup') + 1 != names.index('eric'):
        return False
    if abs(foods.index('spaghetti') - birthdays.index('may')) != 1:
        return False
    if heights.index('very short') >= birthdays.index('april'):
        return False
    if car_models[2] == 'bmw 3 series':
        return False
    if heights.index('very short') != 3:
        return False
    if heights.index('very tall') != car_models.index('toyota camry'):
        return False
    if names.index('alice') + 1 != car_models.index('bmw 3 series'):
        return False
    if car_models.index('tesla model 3') >= heights.index('tall'):
        return False
    if heights.index('tall') != names.index('bob'):
        return False
    if birthdays.index('may') < names.index('alice'):
        return False
    if abs(birthdays.index('sept') - heights.index('very short')) != 1:
        return False
    if abs(birthdays.index('mar') - heights.index('super tall')) != 1:
        return False
    if foods[2] == 'stew':
        return False
    if car_models.index('tesla model 3') != names.index('carol'):
        return False
    if birthdays.index('jan') != names.index('eric'):
        return False
    if birthdays.index('march') != heights.index('short'):
        return False
    if names.index('peter') + 1 != foods.index('pizza'):
        return False
    
    return True

def solve(state, index):
    if index == 6:
        if is_valid(state):
            return state
        else:
            return None
    
    names, birthdays, foods, heights, car_models = state
    
    for i in range(6):
        if i not in [names[index], birthdays[index], foods[index], heights[index], car_models[index]]:
            new_state = (
                names[:index] + [i] + names[index+1:],
                birthdays[:index] + [i] + birthdays[index+1:],
                foods[:index] + [i] + foods[index+1:],
                heights[:index] + [i] + heights[index+1:],
                car_models[:index] + [i] + car_models[index+1:]
            )
            
            result = solve(new_state, index + 1)
            if result:
                return result
    
    return None

# Initialize the state with -1 indicating unassigned
initial_state = ([0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5])

# Solve the puzzle
solution = solve(initial_state, 0)

# Map indices to actual values
names = ["arnold", "carol", "eric", "bob", "alice", "peter"]
birthdays = ["feb", "mar", "sept", "jan", "may", "april"]
foods = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
heights = ["very short", "average", "super tall", "short", "very tall", "tall"]
car_models = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

# Format the solution as JSON
json_solution = {
    "solution": {
        "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
        "rows": []
    }
}

for house in range(6):
    json_solution["solution"]["rows"].append([
        str(house + 1),
        names[solution[0][house]],
        birthdays[solution[1][house]],
        foods[solution[2][house]],
        heights[solution[3][house]],
        car_models[solution[4][house]]
    ])

print(json.dumps(json_solution, indent=2))