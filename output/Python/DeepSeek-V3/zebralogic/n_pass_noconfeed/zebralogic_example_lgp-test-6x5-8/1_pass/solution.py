import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Arnold', 'Peter', 'Bob', 'Eric', 'Carol', 'Alice']
    animals = ['horse', 'rabbit', 'fish', 'cat', 'bird', 'dog']
    occupations = ['engineer', 'nurse', 'lawyer', 'teacher', 'artist', 'doctor']
    sports = ['basketball', 'volleyball', 'soccer', 'tennis', 'baseball', 'swimming']
    heights = ['average', 'tall', 'short', 'very short', 'very tall', 'super tall']
    
    houses = [1, 2, 3, 4, 5, 6]
    
    # Try all permutations until we find one that satisfies all constraints
    for name_perm in permutations(names):
        for animal_perm in permutations(animals):
            for occupation_perm in permutations(occupations):
                for sport_perm in permutations(sports):
                    for height_perm in permutations(heights):
                        # Create assignment dictionaries
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                'name': name_perm[i],
                                'animal': animal_perm[i],
                                'occupation': occupation_perm[i],
                                'sport': sport_perm[i],
                                'height': height_perm[i]
                            }
                        
                        # Check all constraints
                        # 1. The person who is an engineer is the dog owner.
                        engineer_house = None
                        dog_house = None
                        for house in houses:
                            if assignment[house]['occupation'] == 'engineer':
                                engineer_house = house
                            if assignment[house]['animal'] == 'dog':
                                dog_house = house
                        if engineer_house != dog_house:
                            continue
                            
                        # 2. The person who has an average height is somewhere to the left of the person who is short.
                        avg_height_house = None
                        short_height_house = None
                        for house in houses:
                            if assignment[house]['height'] == 'average':
                                avg_height_house = house
                            if assignment[house]['height'] == 'short':
                                short_height_house = house
                        if not (avg_height_house and short_height_house and avg_height_house < short_height_house):
                            continue
                            
                        # 3. The person who has an average height is directly left of the rabbit owner.
                        rabbit_house = None
                        for house in houses:
                            if assignment[house]['animal'] == 'rabbit':
                                rabbit_house = house
                        if not (avg_height_house and rabbit_house and avg_height_house + 1 == rabbit_house):
                            continue
                            
                        # 4. The person who is tall is somewhere to the left of the person who is very short.
                        tall_house = None
                        very_short_house = None
                        for house in houses:
                            if assignment[house]['height'] == 'tall':
                                tall_house = house
                            if assignment[house]['height'] == 'very short':
                                very_short_house = house
                        if not (tall_house and very_short_house and tall_house < very_short_house):
                            continue
                            
                        # 5. Arnold is the cat lover.
                        arnold_house = None
                        cat_house = None
                        for house in houses:
                            if assignment[house]['name'] == 'Arnold':
                                arnold_house = house
                            if assignment[house]['animal'] == 'cat':
                                cat_house = house
                        if arnold_house != cat_house:
                            continue
                            
                        # 6. The person who keeps horses is the person who is a teacher.
                        horse_house = None
                        teacher_house = None
                        for house in houses:
                            if assignment[house]['animal'] == 'horse':
                                horse_house = house
                            if assignment[house]['occupation'] == 'teacher':
                                teacher_house = house
                        if horse_house != teacher_house:
                            continue
                            
                        # 7. Carol is the person who loves soccer.
                        carol_house = None
                        soccer_house = None
                        for house in houses:
                            if assignment[house]['name'] == 'Carol':
                                carol_house = house
                            if assignment[house]['sport'] == 'soccer':
                                soccer_house = house
                        if carol_house != soccer_house:
                            continue
                            
                        # 8. The person who is tall is the person who loves volleyball.
                        volleyball_house = None
                        for house in houses:
                            if assignment[house]['sport'] == 'volleyball':
                                volleyball_house = house
                        if tall_house != volleyball_house:
                            continue
                            
                        # 9. The person who is a lawyer is in the fifth house.
                        if assignment[5]['occupation'] != 'lawyer':
                            continue
                            
                        # 10. The person who loves tennis is the person who is a teacher.
                        tennis_house = None
                        for house in houses:
                            if assignment[house]['sport'] == 'tennis':
                                tennis_house = house
                        if tennis_house != teacher_house:
                            continue
                            
                        # 11. The person who has an average height is the person who loves swimming.
                        swimming_house = None
                        for house in houses:
                            if assignment[house]['sport'] == 'swimming':
                                swimming_house = house
                        if avg_height_house != swimming_house:
                            continue
                            
                        # 12. The person who loves baseball is directly left of the person who is an engineer.
                        baseball_house = None
                        for house in houses:
                            if assignment[house]['sport'] == 'baseball':
                                baseball_house = house
                        if not (baseball_house and engineer_house and baseball_house + 1 == engineer_house):
                            continue
                            
                        # 13. Peter is the person who is a nurse.
                        peter_house = None
                        nurse_house = None
                        for house in houses:
                            if assignment[house]['name'] == 'Peter':
                                peter_house = house
                            if assignment[house]['occupation'] == 'nurse':
                                nurse_house = house
                        if peter_house != nurse_house:
                            continue
                            
                        # 14. Bob is somewhere to the right of the person who is an artist.
                        bob_house = None
                        artist_house = None
                        for house in houses:
                            if assignment[house]['name'] == 'Bob':
                                bob_house = house
                            if assignment[house]['occupation'] == 'artist':
                                artist_house = house
                        if not (bob_house and artist_house and bob_house > artist_house):
                            continue
                            
                        # 15. The person who is a teacher is directly left of the person who loves soccer.
                        if not (teacher_house and soccer_house and teacher_house + 1 == soccer_house):
                            continue
                            
                        # 16. The rabbit owner is Alice.
                        alice_house = None
                        for house in houses:
                            if assignment[house]['name'] == 'Alice':
                                alice_house = house
                        if rabbit_house != alice_house:
                            continue
                            
                        # 17. The fish enthusiast is Carol.
                        fish_house = None
                        for house in houses:
                            if assignment[house]['animal'] == 'fish':
                                fish_house = house
                        if fish_house != carol_house:
                            continue
                            
                        # 18. The person who loves baseball is in the first house.
                        if baseball_house != 1:
                            continue
                            
                        # 19. The cat lover is somewhere to the right of the person who is very short.
                        if not (cat_house and very_short_house and cat_house > very_short_house):
                            continue
                            
                        # 20. The person who is super tall is in the fifth house.
                        if assignment[5]['height'] != 'super tall':
                            continue
                            
                        # If we get here, all constraints are satisfied
                        # Format the solution
                        result = {
                            "solution": {
                                "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
                                "rows": []
                            }
                        }
                        
                        for house in sorted(houses):
                            row = [
                                str(house),
                                assignment[house]['name'],
                                assignment[house]['animal'],
                                assignment[house]['occupation'],
                                assignment[house]['sport'],
                                assignment[house]['height']
                            ]
                            result["solution"]["rows"].append(row)
                        
                        print(json.dumps(result, indent=2))
                        return
    
    print('{"solution": {"header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"], "rows": []}}')

if __name__ == "__main__":
    main()