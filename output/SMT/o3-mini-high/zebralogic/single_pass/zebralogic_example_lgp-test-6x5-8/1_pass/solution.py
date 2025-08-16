from z3 import *
import json

def main():
    s = Solver()
    houses = 6

    # Create an Int variable for each attribute in every house.
    names = [Int(f"name_{i}") for i in range(houses)]
    animals = [Int(f"animal_{i}") for i in range(houses)]
    occs   = [Int(f"occ_{i}")   for i in range(houses)]
    sports = [Int(f"sport_{i}") for i in range(houses)]
    heights= [Int(f"height_{i}")for i in range(houses)]
    
    # Each category has six distinct values in 0..5.
    for i in range(houses):
        s.add(And(names[i]  >= 0, names[i]  <= 5))
        s.add(And(animals[i]>= 0, animals[i] <= 5))
        s.add(And(occs[i]   >= 0, occs[i]   <= 5))
        s.add(And(sports[i] >= 0, sports[i]  <= 5))
        s.add(And(heights[i]>= 0, heights[i] <= 5))
    
    s.add(Distinct(names))
    s.add(Distinct(animals))
    s.add(Distinct(occs))
    s.add(Distinct(sports))
    s.add(Distinct(heights))
    
    # We'll use the following coding for each category:
    #
    # Names: Arnold=0, Peter=1, Bob=2, Eric=3, Carol=4, Alice=5.
    ARNOLD, PETER, BOB, ERIC, CAROL, ALICE = 0, 1, 2, 3, 4, 5
    
    # Animals: bird=0, dog=1, rabbit=2, horse=3, fish=4, cat=5.
    BIRD, DOG, RABBIT, HORSE, FISH, CAT = 0, 1, 2, 3, 4, 5
    
    # Occupations: engineer=0, nurse=1, lawyer=2, teacher=3, artist=4, doctor=5.
    ENGINEER, NURSE, LAWYER, TEACHER, ARTIST, DOCTOR = 0, 1, 2, 3, 4, 5
    
    # FavoriteSports: baseball=0, swimming=1, volleyball=2, tennis=3, soccer=4, basketball=5.
    BASEBALL, SWIMMING, VOLLEYBALL, TENNIS, SOCCER, BASKETBALL = 0, 1, 2, 3, 4, 5
    
    # Heights: average=0, tall=1, short=2, very short=3, very tall=4, super tall=5.
    AVERAGE, TALL, SHORT, VERY_SHORT, VERY_TALL, SUPER_TALL = 0, 1, 2, 3, 4, 5

    # ----------------- Add the clues -----------------
    # Clue 1: The engineer is the dog owner.
    for i in range(houses):
        # "if occ is ENGINEER then animal is DOG", and vice-versa.
        s.add(If(occs[i] == ENGINEER, animals[i] == DOG, animals[i] != DOG))
    
    # Clue 2: The person who has an average height is somewhere to the left of the person who is short.
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(heights[i] == AVERAGE, heights[j] == SHORT), i < j))
    
    # Clue 3: The person who has an average height is directly left of the rabbit owner.
    for i in range(houses - 1):
        s.add(Implies(heights[i] == AVERAGE, animals[i+1] == RABBIT))
    # Ensure average height is not in the last house.
    s.add(heights[houses - 1] != AVERAGE)
    
    # Clue 4: The person who is tall is somewhere to the left of the person who is very short.
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(heights[i] == TALL, heights[j] == VERY_SHORT), i < j))
    
    # Clue 5: Arnold is the cat lover.
    for i in range(houses):
        s.add(Implies(names[i] == ARNOLD, animals[i] == CAT))
    
    # Clue 6: The person who keeps horses is the teacher.
    for i in range(houses):
        s.add(Implies(animals[i] == HORSE, occs[i] == TEACHER))
        s.add(Implies(occs[i]   == TEACHER, animals[i] == HORSE))
    
    # Clue 7: Carol is the person who loves soccer.
    for i in range(houses):
        s.add(Implies(names[i] == CAROL, sports[i] == SOCCER))
    
    # Clue 8: The person who is tall is the person who loves volleyball.
    for i in range(houses):
        s.add(Implies(heights[i] == TALL, sports[i] == VOLLEYBALL))
        s.add(Implies(sports[i]  == VOLLEYBALL, heights[i] == TALL))
    
    # Clue 9: The lawyer is in the fifth house.
    s.add(occs[4] == LAWYER)  # House index 4 = House 5
    
    # Clue 10: The person who loves tennis is the teacher.
    for i in range(houses):
        s.add(Implies(sports[i] == TENNIS, occs[i] == TEACHER))
        s.add(Implies(occs[i]   == TEACHER, sports[i] == TENNIS))
    
    # Clue 11: The person who has an average height is the person who loves swimming.
    for i in range(houses):
        s.add(Implies(heights[i] == AVERAGE, sports[i] == SWIMMING))
        s.add(Implies(sports[i]  == SWIMMING, heights[i] == AVERAGE))
    
    # Clue 12: The person who loves baseball is directly left of the person who is an engineer.
    for i in range(houses - 1):
        s.add(Implies(sports[i] == BASEBALL, occs[i+1] == ENGINEER))
    
    # Clue 13: Peter is the person who is a nurse.
    for i in range(houses):
        s.add(Implies(names[i] == PETER, occs[i] == NURSE))
    
    # Clue 14: Bob is somewhere to the right of the person who is an artist.
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(occs[j] == ARTIST, names[i] == BOB), j < i))
    
    # Clue 15: The teacher is directly left of the person who loves soccer.
    for i in range(houses - 1):
        s.add(Implies(occs[i] == TEACHER, sports[i+1] == SOCCER))
    s.add(occs[houses - 1] != TEACHER)
    
    # Clue 16: The rabbit owner is Alice.
    for i in range(houses):
        s.add(Implies(names[i] == ALICE, animals[i] == RABBIT))
    
    # Clue 17: The fish enthusiast is Carol.
    for i in range(houses):
        s.add(Implies(names[i] == CAROL, animals[i] == FISH))
    
    # Clue 18: The person who loves baseball is in the first house.
    s.add(sports[0] == BASEBALL)
    
    # Clue 19: The cat lover is somewhere to the right of the person who is very short.
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(heights[i] == VERY_SHORT, animals[j] == CAT), i < j))
    
    # Clue 20: The person who is super tall is in the fifth house.
    s.add(heights[4] == SUPER_TALL)
    
    # ----------------- Solve and output the solution -----------------
    if s.check() == sat:
        m = s.model()
        # Define maps to convert our integer codes back to strings.
        names_map = {
            ARNOLD: "Arnold",
            PETER: "Peter",
            BOB: "Bob",
            ERIC: "Eric",
            CAROL: "Carol",
            ALICE: "Alice"
        }
        animals_map = {
            BIRD: "bird",
            DOG: "dog",
            RABBIT: "rabbit",
            HORSE: "horse",
            FISH: "fish",
            CAT: "cat"
        }
        occ_map = {
            ENGINEER: "engineer",
            NURSE: "nurse",
            LAWYER: "lawyer",
            TEACHER: "teacher",
            ARTIST: "artist",
            DOCTOR: "doctor"
        }
        sports_map = {
            BASEBALL: "baseball",
            SWIMMING: "swimming",
            VOLLEYBALL: "volleyball",
            TENNIS: "tennis",
            SOCCER: "soccer",
            BASKETBALL: "basketball"
        }
        heights_map = {
            AVERAGE: "average",
            TALL: "tall",
            SHORT: "short",
            VERY_SHORT: "very short",
            VERY_TALL: "very tall",
            SUPER_TALL: "super tall"
        }
        
        # Build the solution rows in the fixed order of houses (House 1...House 6)
        solution_rows = []
        for i in range(houses):
            house_num = str(i+1)
            name_str   = names_map[m[names[i]].as_long()]
            animal_str = animals_map[m[animals[i]].as_long()]
            occ_str    = occ_map[m[occs[i]].as_long()]
            sport_str  = sports_map[m[sports[i]].as_long()]
            height_str = heights_map[m[heights[i]].as_long()]
            solution_rows.append([house_num, name_str, animal_str, occ_str, sport_str, height_str])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()