import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Peter", "Bob", "Eric", "Carol", "Alice"]
    animals = ["horse", "rabbit", "fish", "cat", "bird", "dog"]
    occupations = ["engineer", "nurse", "lawyer", "teacher", "artist", "doctor"]
    favorite_sports = ["basketball", "volleyball", "soccer", "tennis", "baseball", "swimming"]
    heights = ["average", "tall", "short", "very short", "very tall", "super tall"]

    for name_perm in itertools.permutations(names):
        for animal_perm in itertools.permutations(animals):
            for occupation_perm in itertools.permutations(occupations):
                for sport_perm in itertools.permutations(favorite_sports):
                    for height_perm in itertools.permutations(heights):
                        # Apply constraints
                        if (occupation_perm[houses.index(name_perm.index("engineer"))] == "dog" and
                            height_perm[houses.index(name_perm.index("average"))] < height_perm[houses.index(name_perm.index("short"))] and
                            height_perm[houses.index(name_perm.index("average"))] + 1 == houses.index(animal_perm.index("rabbit")) and
                            height_perm[houses.index(name_perm.index("tall"))] < height_perm[houses.index(name_perm.index("very short"))] and
                            name_perm[houses.index(animal_perm.index("cat"))] == "Arnold" and
                            occupation_perm[houses.index(animal_perm.index("horse"))] == "teacher" and
                            name_perm[houses.index(sport_perm.index("soccer"))] == "Carol" and
                            sport_perm[houses.index(height_perm.index("tall"))] == "volleyball" and
                            occupation_perm[4] == "lawyer" and
                            sport_perm[houses.index(occupation_perm.index("teacher"))] == "tennis" and
                            sport_perm[houses.index(height_perm.index("average"))] == "swimming" and
                            sport_perm[houses.index(name_perm.index("baseball"))] + 1 == houses.index(name_perm.index("engineer")) and
                            name_perm[houses.index(occupation_perm.index("nurse"))] == "Peter" and
                            name_perm.index("Bob") > name_perm.index(occupation_perm.index("artist")) and
                            houses.index(occupation_perm.index("teacher")) + 1 == houses.index(sport_perm.index("soccer")) and
                            animal_perm[houses.index(name_perm.index("Alice"))] == "rabbit" and
                            animal_perm[houses.index(name_perm.index("Carol"))] == "fish" and
                            sport_perm[0] == "baseball" and
                            animal_perm[houses.index(name_perm.index("cat"))] > height_perm.index("very short") and
                            height_perm[4] == "super tall"):
                            
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
                                    "rows": [
                                        [str(house), name_perm[i], animal_perm[i], occupation_perm[i], sport_perm[i], height_perm[i]]
                                        for i, house in enumerate(houses)
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)

print(solve_puzzle())