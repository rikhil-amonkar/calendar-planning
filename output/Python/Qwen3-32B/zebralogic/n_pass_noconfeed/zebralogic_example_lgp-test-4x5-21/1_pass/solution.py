import itertools
import json

def main():
    # Define the categories
    names = ['Eric', 'Alice', 'Peter', 'Arnold']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    sports = ['soccer', 'tennis', 'basketball', 'swimming']
    cars = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']
    flowers = ['daffodils', 'roses', 'lilies', 'carnations']

    # Generate permutations for each category
    name_perms = list(itertools.permutations(names))
    smoothie_perms = list(itertools.permutations(smoothies))
    # Pre-filter sport permutations: first is tennis, second is soccer
    sport_perms = [p for p in itertools.permutations(sports) if p[0] == 'tennis' and p[1] == 'soccer']
    car_perms = list(itertools.permutations(cars))
    flower_perms = list(itertools.permutations(flowers))

    # Iterate through all combinations
    for name_p in name_perms:
        for smoothie_p in smoothie_perms:
            for sport_p in sport_perms:
                for car_p in car_perms:
                    for flower_p in flower_perms:
                        # Check all constraints
                        # Check clue 1: Tesla Model 3 owner loves roses
                        valid = True
                        for i in range(4):
                            if car_p[i] == 'tesla model 3' and flower_p[i] != 'roses':
                                valid = False
                                break
                        if not valid:
                            continue
                        # Check clue 2: Peter's smoothie is dragonfruit
                        peter_idx = name_p.index('Peter')
                        if smoothie_p[peter_idx] != 'dragonfruit':
                            continue
                        # Check clue 3: Desert lover has Toyota Camry
                        for i in range(4):
                            if smoothie_p[i] == 'desert' and car_p[i] != 'toyota camry':
                                valid = False
                                break
                        if not valid:
                            continue
                        # Check clue 5: Toyota Camry and basketball are next to each other
                        tc_idx = car_p.index('toyota camry')
                        basketball_idx = sport_p.index('basketball')
                        if abs(tc_idx - basketball_idx) != 1:
                            continue
                        # Check clue 6: Arnold's sport is basketball
                        arnold_idx = name_p.index('Arnold')
                        if sport_p[arnold_idx] != 'basketball':
                            continue
                        # Check clue 7: Honda Civic owner loves daffodils
                        hc_idx = car_p.index('honda civic')
                        if flower_p[hc_idx] != 'daffodils':
                            continue
                        # Check clue 8: Eric loves roses
                        eric_idx = name_p.index('Eric')
                        if flower_p[eric_idx] != 'roses':
                            continue
                        # Check clue 9: Watermelon not in first house
                        if smoothie_p[0] == 'watermelon':
                            continue
                        # Check clue 10: Honda Civic is to the right of Desert lover
                        desert_idx = smoothie_p.index('desert')
                        hc_idx = car_p.index('honda civic')
                        if hc_idx <= desert_idx:
                            continue
                        # Check clue 11: Basketball lover loves lilies
                        basketball_idx = sport_p.index('basketball')
                        if flower_p[basketball_idx] != 'lilies':
                            continue
                        # If all constraints passed, build the solution
                        rows = []
                        for i in range(4):
                            house_num = str(i + 1)
                            name = name_p[i]
                            smoothie = smoothie_p[i]
                            sport = sport_p[i]
                            car = car_p[i]
                            flower = flower_p[i]
                            rows.append([house_num, name, smoothie, sport, car, flower])
                        # Output the JSON
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
                                "rows": rows
                            }
                        }
                        print(json.dumps(solution, indent=2))
                        return  # Assuming only one solution exists

if __name__ == "__main__":
    main()