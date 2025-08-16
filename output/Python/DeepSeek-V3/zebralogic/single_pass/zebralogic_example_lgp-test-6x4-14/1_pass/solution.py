import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
    car_models = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
    mothers = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
    hobbies = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']

    # Initialize solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
            "rows": []
        }
    }

    # Generate all possible permutations for each category (brute-force is impractical, so we'll use constraints to narrow down)
    # Instead, we'll use a backtracking approach with constraints

    # Let's create a dictionary to hold the assignments
    assignments = {house: {'Name': None, 'CarModel': None, 'Mother': None, 'Hobby': None} for house in houses}

    # Apply direct clues first
    # Clue 1: The person who owns a Toyota Camry is in the sixth house.
    assignments[6]['CarModel'] = 'toyota camry'

    # Clue 7: The person whose mother's name is Kailyn is in the sixth house.
    assignments[6]['Mother'] = 'Kailyn'

    # Clue 16: The person who owns a Honda Civic is Arnold.
    # So in some house, Name is Arnold and CarModel is honda civic

    # Clue 6: The person who owns a BMW 3 Series is Bob.
    # So in some house, Name is Bob and CarModel is bmw 3 series

    # Clue 2: Carol is the photography enthusiast.
    # So in some house, Name is Carol and Hobby is photography

    # Clue 13: Eric is the person who enjoys gardening.
    # So in some house, Name is Eric and Hobby is gardening

    # Clue 5: The person who owns a Ford F-150 is the person whose mother's name is Sarah.
    # So in some house, CarModel is ford f150 and Mother is Sarah

    # Clue 9: There is one house between the person whose mother's name is Sarah and the person who owns a Toyota Camry.
    # Toyota Camry is in house 6, so Sarah's mother is in house 4 (since 4 + 2 = 6)
    assignments[4]['Mother'] = 'Sarah'
    assignments[4]['CarModel'] = 'ford f150'  # from clue 5

    # Clue 15: There is one house between the person whose mother's name is Sarah (house 4) and the person who loves cooking.
    # So cooking is in house 6 (4 + 2 = 6), but house 6's hobby isn't assigned yet
    # But house 6's mother is Kailyn, let's see if this conflicts
    # Assign cooking to house 6
    assignments[6]['Hobby'] = 'cooking'

    # Clue 12: Alice is somewhere to the right of the person who owns a Ford F-150 (house 4)
    # So Alice is in house 5 or 6
    # But house 6's name isn't assigned yet, but let's see other clues

    # Clue 8: Eric is directly left of the person who enjoys knitting.
    # So Eric is in house X, knitting is in house X+1

    # Clue 17: The person whose mother's name is Holly is directly left of the person who enjoys knitting.
    # So Holly is in house Y, knitting is in Y+1
    # Therefore, Eric is in Y, because both Eric and Holly are directly left of knitting
    # So Y must be the same as X, meaning Eric's mother is Holly
    # So in house X: Name is Eric, Mother is Holly
    # And house X+1: Hobby is knitting

    # Clue 14: The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
    # So woodworking is in house < X+1

    # Clue 10: The person whose mother's name is Penny is somewhere to the right of the person who enjoys knitting.
    # So Penny is in house > X+1

    # Clue 4: The person who owns a Chevrolet Silverado is not in the second house.
    # From clue 3: The person who owns a Chevrolet Silverado is the person whose mother's name is Aniya.
    # So in some house not 2: CarModel is chevrolet silverado and Mother is Aniya

    # Clue 11: The person whose mother's name is Aniya is somewhere to the right of the person who owns a Honda Civic.
    # So honda civic is left of Aniya (chevrolet silverado)

    # Clue 16: The person who owns a Honda Civic is Arnold.
    # So in some house: Name is Arnold, CarModel is honda civic

    # Let's find possible positions for Eric and knitting
    # Eric is in X, knitting in X+1
    # From clue 17, Eric's mother is Holly
    # Possible X values: 1,2,3,4,5 (since X+1 must be <=6)
    # But house 4 has mother Sarah, so X can't be 4
    # Also, from clue 14, woodworking is left of knitting (so woodworking is in <X+1)
    # From clue 10, Penny is right of knitting (so Penny is in >X+1)
    # From clue 12, Alice is right of house 4 (so 5 or 6)
    # Let's try X=1:
    # House 1: Name Eric, Mother Holly
    # House 2: Hobby knitting
    # Then woodworking must be left of 2, so house 1
    # But house 1's hobby isn't assigned yet, could be woodworking
    # Then Penny is right of 2, so 3,4,5,6
    # But house 4's mother is Sarah, house 6's is Kailyn, so Penny is in 3 or 5
    # From clue 3 and 11: honda civic is left of chevrolet silverado (Aniya)
    # Arnold is honda civic, so Arnold is left of Aniya
    # Let's assign Arnold to house 1, but house 1's name is Eric, so no
    # Assign Arnold to house 2 or 3
    # House 2: hobby is knitting, name could be Arnold
    # Then car is honda civic
    assignments[2]['Name'] = 'Arnold'
    assignments[2]['CarModel'] = 'honda civic'
    assignments[2]['Hobby'] = 'knitting'
    # Then house 1: name Eric, mother Holly, hobby?
    assignments[1]['Name'] = 'Eric'
    assignments[1]['Mother'] = 'Holly'
    # From clue 13, Eric enjoys gardening
    assignments[1]['Hobby'] = 'gardening'
    # So woodworking must be left of knitting (house 2), but house 1's hobby is gardening, so this contradicts clue 14
    # So X=1 is invalid

    # Try X=2:
    # House 2: Name Eric, Mother Holly
    # House 3: Hobby knitting
    # woodworking is left of 3, so 1 or 2
    # house 2's hobby not assigned yet, could be woodworking
    assignments[2]['Hobby'] = 'woodworking'
    # Penny is right of 3, so 4,5,6
    # house 4 mother is Sarah, 6 is Kailyn, so Penny is in 5
    assignments[5]['Mother'] = 'Penny'
    # From clue 16: Arnold owns honda civic
    # Must be left of Aniya (chevrolet silverado)
    # Possible positions: 1 or 3 or 4
    # house 4's car is ford f150, so not honda civic
    # house 3: hobby is knitting, could be name Arnold
    assignments[3]['Name'] = 'Arnold'
    assignments[3]['CarModel'] = 'honda civic'
    # Then Aniya is right of honda civic, so house 4 or 5 or 6
    # house 4's mother is Sarah, 6 is Kailyn, so Aniya is in 5
    assignments[5]['Mother'] = 'Aniya'  # But earlier we had Penny in 5, conflict
    # So this path is invalid

    # Try X=3:
    # House 3: Name Eric, Mother Holly
    # House 4: Hobby knitting
    # But house 4's mother is Sarah, and car is ford f150
    # woodworking is left of 4, so 1,2,3
    # house 3's hobby could be woodworking
    assignments[3]['Hobby'] = 'woodworking'
    # Penny is right of 4, so 5 or 6
    # house 6's mother is Kailyn, so Penny is in 5
    assignments[5]['Mother'] = 'Penny'
    # Arnold is honda civic, must be left of Aniya
    # Possible positions: 1 or 2
    assignments[1]['Name'] = 'Arnold'
    assignments[1]['CarModel'] = 'honda civic'
    # Then Aniya is right of 1, so 2,3,4,5,6
    # house 3's mother is Holly, 4 is Sarah, 5 is Penny, 6 is Kailyn, so Aniya is in 2
    assignments[2]['Mother'] = 'Aniya'
    # From clue 3: chevrolet silverado is Aniya's car
    assignments[2]['CarModel'] = 'chevrolet silverado'
    # From clue 4: chevrolet not in 2, but we have it in 2, conflict
    # So invalid path

    # Try X=5:
    # House 5: Name Eric, Mother Holly
    # House 6: Hobby knitting
    # But house 6's hobby is cooking from earlier, conflict
    # So invalid

    # Only remaining is X=3 with adjustments
    # Let me retry X=3 with different assignments
    # House 3: Name Eric, Mother Holly, Hobby gardening (from clue 13)
    assignments[3]['Name'] = 'Eric'
    assignments[3]['Mother'] = 'Holly'
    assignments[3]['Hobby'] = 'gardening'
    # House 4: Hobby knitting
    assignments[4]['Hobby'] = 'knitting'
    # woodworking is left of 4, so 1,2,3
    assignments[1]['Hobby'] = 'woodworking'
    # Penny is right of 4, so 5 or 6
    assignments[5]['Mother'] = 'Penny'
    # Arnold is honda civic, left of Aniya
    assignments[2]['Name'] = 'Arnold'
    assignments[2]['CarModel'] = 'honda civic'
    # Aniya is right of 2, so 3,4,5,6
    # 3 mother is Holly, 4 is Sarah, 6 is Kailyn, so 5
    assignments[5]['Mother'] = 'Aniya'  # But earlier we have Penny in 5, conflict
    # Alternative: maybe Aniya is in 3, but 3 is Holly
    # So this path seems invalid

    # Let me try X=2 again with different assignments
    # House 2: Name Eric, Mother Holly, Hobby gardening
    assignments[2]['Name'] = 'Eric'
    assignments[2]['Mother'] = 'Holly'
    assignments[2]['Hobby'] = 'gardening'
    # House 3: Hobby knitting
    assignments[3]['Hobby'] = 'knitting'
    # woodworking is left of 3, so 1
    assignments[1]['Hobby'] = 'woodworking'
    # Penny is right of 3, so 4,5,6
    # 4 mother is Sarah, 6 is Kailyn, so 5
    assignments[5]['Mother'] = 'Penny'
    # Arnold is honda civic, left of Aniya
    assignments[1]['Name'] = 'Arnold'
    assignments[1]['CarModel'] = 'honda civic'
    # Aniya is right of 1, so 2,3,4,5,6
    # 2 mother is Holly, 4 is Sarah, 5 is Penny, 6 is Kailyn, so 3
    assignments[3]['Mother'] = 'Aniya'
    # From clue 3: chevrolet silverado is Aniya's car
    assignments[3]['CarModel'] = 'chevrolet silverado'
    # From clue 4: chevrolet not in 2, which is satisfied
    # From clue 6: bmw 3 series is Bob
    # Bob must be in remaining houses: 4,5,6
    # house 4: name not assigned
    assignments[4]['Name'] = 'Bob'
    assignments[4]['CarModel'] = 'bmw 3 series'
    # house 5: name not assigned, remaining names: Peter, Alice, Carol
    # house 6: name not assigned
    # From clue 2: Carol is photography
    # photography not assigned yet, possible in 5 or 6
    # house 6's hobby is cooking, so Carol must be in 5
    assignments[5]['Name'] = 'Carol'
    assignments[5]['Hobby'] = 'photography'
    # house 6's name is remaining: Alice or Peter
    # From clue 12: Alice is right of ford f150 (house 4)
    # house 4 has bmw 3 series, not ford f150, wait no:
    # house 4's car is bmw 3 series, but ford f150 is in house 4? No, earlier we have ford f150 in house 4
    # Wait, from clue 5: ford f150 is mother Sarah, which is house 4
    # So house 4's car is ford f150, not bmw 3 series
    # Conflict: house 4's car was assigned bmw from Bob, but ford is from mother Sarah
    # So need to reassign
    assignments[4]['CarModel'] = 'ford f150'  # from clue 5
    # Then bmw must be elsewhere
    # Bob must be in house 5 or 6
    # house 5's name is Carol, so Bob is in 6
    assignments[6]['Name'] = 'Bob'
    assignments[6]['CarModel'] = 'bmw 3 series'
    # Then house 5's name is Carol
    # house 4's name is remaining: Peter or Alice
    # From clue 12: Alice is right of ford f150 (house 4), so Alice must be right of 4, so 5 or 6
    # 5 is Carol, 6 is Bob, so Alice is not possible, meaning our assignments are invalid
    # Alternative: maybe house 4's name is Alice
    assignments[4]['Name'] = 'Alice'
    # Then Bob must be in 5 or 6
    # 5 is Carol, so Bob in 6
    assignments[6]['Name'] = 'Bob'
    assignments[6]['CarModel'] = 'bmw 3 series'
    # house 5's name is Carol
    assignments[5]['Name'] = 'Carol'
    assignments[5]['Hobby'] = 'photography'
    # house 4's name is Alice
    # From clue 12: Alice is right of ford f150 (house 4), but Alice is in 4, so this is invalid
    # So Alice must be right of 4, meaning in 5 or 6
    # 5 is Carol, 6 is Bob, so no Alice possible, contradiction

    # Let me try a different approach: maybe house 1 is not Arnold
    # Reset assignments where needed
    assignments = {house: {'Name': None, 'CarModel': None, 'Mother': None, 'Hobby': None} for house in houses}
    assignments[6]['CarModel'] = 'toyota camry'
    assignments[6]['Mother'] = 'Kailyn'
    assignments[4]['Mother'] = 'Sarah'
    assignments[4]['CarModel'] = 'ford f150'
    assignments[6]['Hobby'] = 'cooking'

    # Try Eric in house 1
    assignments[1]['Name'] = 'Eric'
    assignments[1]['Mother'] = 'Holly'
    assignments[1]['Hobby'] = 'gardening'
    # knitting in 2
    assignments[2]['Hobby'] = 'knitting'
    # woodworking left of 2, so 1
    assignments[1]['Hobby'] = 'woodworking'  # but Eric is gardening, conflict
    # So invalid

    # Final attempt: Eric in 3, knitting in 4
    assignments[3]['Name'] = 'Eric'
    assignments[3]['Mother'] = 'Holly'
    assignments[3]['Hobby'] = 'gardening'
    assignments[4]['Hobby'] = 'knitting'
    # woodworking left of 4: 1,2,3
    assignments[1]['Hobby'] = 'woodworking'
    # Penny right of 4: 5
    assignments[5]['Mother'] = 'Penny'
    # Arnold is honda civic, left of Aniya
    assignments[2]['Name'] = 'Arnold'
    assignments[2]['CarModel'] = 'honda civic'
    # Aniya is right of 2: 3,4,5,6
    # 3 is Holly, 4 is Sarah, 6 is Kailyn, so 5
    assignments[5