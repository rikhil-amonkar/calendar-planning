import json

def main():
    # Define the attributes and their possible values
    names = ['Arnold', 'Peter', 'Bob', 'Eric', 'Carol', 'Alice']
    animals = ['horse', 'rabbit', 'fish', 'cat', 'bird', 'dog']
    occupations = ['engineer', 'nurse', 'lawyer', 'teacher', 'artist', 'doctor']
    sports = ['basketball', 'volleyball', 'soccer', 'tennis', 'baseball', 'swimming']
    heights = ['average', 'tall', 'short', 'very short', 'very tall', 'super tall']
    
    # Deduced solution
    solution = [
        ('Peter', 'bird', 'nurse', 'baseball', 'very tall'),
        ('Eric', 'dog', 'engineer', 'swimming', 'average'),
        ('Alice', 'rabbit', 'artist', 'volleyball', 'tall'),
        ('Bob', 'horse', 'teacher', 'tennis', 'very short'),
        ('Carol', 'fish', 'lawyer', 'soccer', 'super tall'),
        ('Arnold', 'cat', 'doctor', 'basketball', 'short')
    ]
    
    # Map house indices to attributes
    house_solution = []
    for i in range(6):
        name, animal, occupation, sport, height = solution[i]
        house_solution.append({
            'House': str(i+1),
            'Name': name,
            'Animal': animal,
            'Occupation': occupation,
            'Sport': sport,
            'Height': height
        })
    
    # Verify the solution against all clues
    def verify_solution():
        # Create index maps for quick lookup
        name_to_house = {}
        animal_to_house = {}
        occupation_to_house = {}
        sport_to_house = {}
        height_to_house = {}
        for i, (name, animal, occupation, sport, height) in enumerate(solution):
            name_to_house[name] = i
            animal_to_house[animal] = i
            occupation_to_house[occupation] = i
            sport_to_house[sport] = i
            height_to_house[height] = i
        
        # Clue 1: The person who is an engineer is the dog owner.
        if occupation_to_house['engineer'] != animal_to_house['dog']:
            return False
        
        # Clue 2: The person who has an average height is somewhere to the left of the person who is short.
        if height_to_house['average'] >= height_to_house['short']:
            return False
        
        # Clue 3: The person who has an average height is directly left of the rabbit owner.
        if height_to_house['average'] + 1 != animal_to_house['rabbit']:
            return False
        
        # Clue 4: The person who is tall is somewhere to the left of the person who is very short.
        if height_to_house['tall'] >= height_to_house['very short']:
            return False
        
        # Clue 5: Arnold is the cat lover.
        if animal_to_house['cat'] != name_to_house['Arnold']:
            return False
        
        # Clue 6: The person who keeps horses is the person who is a teacher.
        if animal_to_house['horse'] != occupation_to_house['teacher']:
            return False
        
        # Clue 7: Carol is the person who loves soccer.
        if sport_to_house['soccer'] != name_to_house['Carol']:
            return False
        
        # Clue 8: The person who is tall is the person who loves volleyball.
        if height_to_house['tall'] != sport_to_house['volleyball']:
            return False
        
        # Clue 9: The person who is a lawyer is in the fifth house.
        if occupation_to_house['lawyer'] != 4:
            return False
        
        # Clue 10: The person who loves tennis is the person who is a teacher.
        if sport_to_house['tennis'] != occupation_to_house['teacher']:
            return False
        
        # Clue 11: The person who has an average height is the person who loves swimming.
        if height_to_house['average'] != sport_to_house['swimming']:
            return False
        
        # Clue 12: The person who loves baseball is directly left of the person who is an engineer.
        if sport_to_house['baseball'] + 1 != occupation_to_house['engineer']:
            return False
        
        # Clue 13: Peter is the person who is a nurse.
        if occupation_to_house['nurse'] != name_to_house['Peter']:
            return False
        
        # Clue 14: Bob is somewhere to the right of the person who is an artist.
        if name_to_house['Bob'] <= occupation_to_house['artist']:
            return False
        
        # Clue 15: The person who is a teacher is directly left of the person who loves soccer.
        if occupation_to_house['teacher'] + 1 != sport_to_house['soccer']:
            return False
        
        # Clue 16: The rabbit owner is Alice.
        if animal_to_house['rabbit'] != name_to_house['Alice']:
            return False
        
        # Clue 17: The fish enthusiast is Carol.
        if animal_to_house['fish'] != name_to_house['Carol']:
            return False
        
        # Clue 18: The person who loves baseball is in the first house.
        if sport_to_house['baseball'] != 0:
            return False
        
        # Clue 19: The cat lover is somewhere to the right of the person who is very short.
        if name_to_house['Arnold'] <= height_to_house['very short']:
            return False
        
        # Clue 20: The person who is super tall is in the fifth house.
        if height_to_house['super tall'] != 4:
            return False
        
        return True
    
    if not verify_solution():
        print('{"error": "The solution is invalid"}')
        return
    
    # Format the solution as JSON
    output = {
        "solution": {
            "header": ["House", "Name", "Animal", "Occupation", "Sport", "Height"],
            "rows": []
        }
    }
    for house in house_solution:
        row = [
            house['House'],
            house['Name'],
            house['Animal'],
            house['Occupation'],
            house['Sport'],
            house['Height']
        ]
        output["solution"]["rows"].append(row)
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()