import itertools
import json

# Define the possible values for each category
names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
animals = ["horse", "dog", "bird", "fish", "cat"]
nationalities = ["german", "swede", "norwegian", "brit", "dane"]

# Initialize the houses with empty dictionaries
houses = [{}, {}, {}, {}, {}]

def is_valid_solution(houses):
    # Unpack the houses for easier access
    h1, h2, h3, h4, h5 = houses
    
    # Apply each clue
    # 1. The Swedish person is directly left of the dog owner.
    if h1.get("Nationality") == "swede" and h2.get("Animal") != "dog":
        return False
    if h2.get("Nationality") == "swede" and h3.get("Animal") != "dog":
        return False
    if h3.get("Nationality") == "swede" and h4.get("Animal") != "dog":
        return False
    if h4.get("Nationality") == "swede" and h5.get("Animal") != "dog":
        return False
    
    # 2. There are two houses between the dog owner and the British person.
    dog_house = [i+1 for i, h in enumerate(houses) if h.get("Animal") == "dog"][0]
    brit_house = [i+1 for i, h in enumerate(houses) if h.get("Nationality") == "brit"][0]
    if abs(dog_house - brit_house) != 3:
        return False
    
    # 3. The Dane is the person who keeps horses.
    if h3.get("Nationality") != "dane" or h3.get("Animal") != "horse":
        return False
    
    # 4. The bird keeper is somewhere to the right of the cat lover.
    cat_house = [i+1 for i, h in enumerate(houses) if h.get("Animal") == "cat"][0]
    bird_house = [i+1 for i, h in enumerate(houses) if h.get("Animal") == "bird"][0]
    if cat_house >= bird_house:
        return False
    
    # 5. The dog owner is directly left of the person who drinks Lime smoothies.
    if dog_house + 1 != [i+1 for i, h in enumerate(houses) if h.get("Smoothie") == "lime"][0]:
        return False
    
    # 6. Eric is the cat lover.
    if [h.get("Name") for h in houses if h.get("Animal") == "cat"][0] != "Eric":
        return False
    
    # 7. Bob is the bird keeper.
    if [h.get("Name") for h in houses if h.get("Animal") == "bird"][0] != "Bob":
        return False
    
    # 8. The person who likes Cherry smoothies is directly left of Peter.
    cherry_house = [i+1 for i, h in enumerate(houses) if h.get("Smoothie") == "cherry"][0]
    if cherry_house + 1 != [i+1 for i, h in enumerate(houses) if h.get("Name") == "Peter"][0]:
        return False
    
    # 9. The bird keeper is the Watermelon smoothie lover.
    if [h.get("Smoothie") for h in houses if h.get("Animal") == "bird"][0] != "watermelon":
        return False
    
    # 10. The Desert smoothie lover is the dog owner.
    if [h.get("Smoothie") for h in houses if h.get("Animal") == "dog"][0] != "desert":
        return False
    
    # 11. The person who keeps horses is in the third house.
    if h3.get("Animal") != "horse":
        return False
    
    # 12. The Norwegian is Alice.
    if [h.get("Nationality") for h in houses if h.get("Name") == "Alice"][0] != "norwegian":
        return False
    
    return True

# Generate all permutations for each category
all_permutations = list(itertools.permutations(names)) * \
                   list(itertools.permutations(smoothies)) * \
                   list(itertools.permutations(animals)) * \
                   list(itertools.permutations(nationalities))

# Try each combination
for names_perm in itertools.permutations(names):
    for smoothies_perm in itertools.permutations(smoothies):
        for animals_perm in itertools.permutations(animals):
            for nationalities_perm in itertools.permutations(nationalities):
                # Assign the permutations to the houses
                for i in range(5):
                    houses[i]["Name"] = names_perm[i]
                    houses[i]["Smoothie"] = smoothies_perm[i]
                    houses[i]["Animal"] = animals_perm[i]
                    houses[i]["Nationality"] = nationalities_perm[i]
                
                # Check if the current assignment is valid
                if is_valid_solution(houses):
                    # Format the solution as required
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                            "rows": [
                                [str(i+1), houses[i]["Name"], houses[i]["Smoothie"], houses[i]["Animal"], houses[i]["Nationality"]]
                                for i in range(5)
                            ]
                        }
                    }
                    
                    # Output the solution as JSON
                    print(json.dumps(solution, indent=2))
                    exit()