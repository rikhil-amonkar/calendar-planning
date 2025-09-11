import itertools
import json

# Fixed data based on constraints
names = ["Eric", "Arnold", "Peter"]
house_styles = ["ranch", "colonial", "victorian"]
heights = ["average", "short", "very short"]

phone_models = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
car_models = ['tesla model 3', 'toyota camry', 'ford f150']

solution = None

# Generate all permutations for phone and car models
for phone_perm in itertools.permutations(phone_models):
    # Check clue 4: Samsung in house 3 (index 2)
    if phone_perm[2] != 'samsung galaxy s21':
        continue
    # Check clue 5: iPhone directly left of Google Pixel
    if phone_perm[0] != 'iphone 13' or phone_perm[1] != 'google pixel 6':
        continue

    for car_perm in itertools.permutations(car_models):
        # Check clue 3: Tesla in house 3 (very short)
        if car_perm[2] != 'tesla model 3':
            continue
        # Check clue 8: Ford is to the right of Toyota
        toy_idx = car_perm.index('toyota camry')
        ford_idx = car_perm.index('ford f150')
        if ford_idx <= toy_idx:
            continue

        # Build the solution if all constraints are met
        solution = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                "rows": []
            }
        }
        for i in range(3):
            house_num = i + 1
            solution["solution"]["rows"].append([
                str(house_num),
                names[i],
                phone_perm[i],
                heights[i],
                house_styles[i],
                car_perm[i]
            ])
        break  # Exit car_perm loop once solution is found
    if solution:
        break  # Exit phone_perm loop once solution is found

# Output the solution as JSON
print(json.dumps(solution, indent=2))