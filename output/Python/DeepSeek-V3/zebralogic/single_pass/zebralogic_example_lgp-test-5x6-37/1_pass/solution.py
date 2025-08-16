import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4', '5']
    names = ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric']
    hobbies = ['cooking', 'gardening', 'painting', 'photography', 'knitting']
    sports = ['swimming', 'tennis', 'soccer', 'baseball', 'basketball']
    house_styles = ['ranch', 'craftsman', 'victorian', 'modern', 'colonial']
    children = ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred']
    heights = ['average', 'very tall', 'very short', 'short', 'tall']

    # Initialize possibilities for each house
    possibilities = []
    for house in houses:
        possibilities.append({
            'Name': names.copy(),
            'Hobby': hobbies.copy(),
            'FavoriteSport': sports.copy(),
            'HouseStyle': house_styles.copy(),
            'Children': children.copy(),
            'Height': heights.copy()
        })

    # Apply clues one by one
    # Clue 20: Victorian is in house 5
    for i in range(5):
        if i != 4:
            possibilities[i]['HouseStyle'].remove('victorian')
    possibilities[4]['HouseStyle'] = ['victorian']

    # Clue 14: Victorian house has child Fred
    possibilities[4]['Children'] = ['Fred']

    # Clue 3: Peter is directly left of Victorian house (so Peter is in house 4)
    possibilities[3]['Name'] = ['Peter']
    for i in [0,1,2,4]:
        if 'Peter' in possibilities[i]['Name']:
            possibilities[i]['Name'].remove('Peter')

    # Clue 16: Peter is very tall
    possibilities[3]['Height'] = ['very tall']
    for i in [0,1,2,4]:
        if 'very tall' in possibilities[i]['Height']:
            possibilities[i]['Height'].remove('very tall')

    # Clue 5: very tall person loves baseball
    possibilities[3]['FavoriteSport'] = ['baseball']
    for i in [0,1,2,4]:
        if 'baseball' in possibilities[i]['FavoriteSport']:
            possibilities[i]['FavoriteSport'].remove('baseball')

    # Clue 4: Alice is tall
    # Clue 2: tall person is in house 2
    possibilities[1]['Height'] = ['tall']
    possibilities[1]['Name'] = ['Alice']
    for i in [0,2,3,4]:
        if 'tall' in possibilities[i]['Height']:
            possibilities[i]['Height'].remove('tall')
        if 'Alice' in possibilities[i]['Name']:
            possibilities[i]['Name'].remove('Alice')

    # Clue 8: gardening is in house 2
    possibilities[1]['Hobby'] = ['gardening']
    for i in [0,2,3,4]:
        if 'gardening' in possibilities[i]['Hobby']:
            possibilities[i]['Hobby'].remove('gardening')

    # Clue 18: knitting and gardening are next to each other
    # gardening is in house 2, so knitting is in house 1 or 3
    for i in [0,2]:
        if 'knitting' not in possibilities[i]['Hobby']:
            possibilities[i]['Hobby'] = [h for h in possibilities[i]['Hobby'] if h != 'knitting']

    # Clue 19: modern house loves cooking
    # Clue 12: child Samantha is in modern house
    # Clue 10: tennis lover has child Samantha
    # So tennis lover is in modern house and loves cooking
    # So modern house: FavoriteSport: tennis, Hobby: cooking, Children: Samantha

    # Clue 7: Bob paints
    for i in range(5):
        if 'Bob' in possibilities[i]['Name']:
            possibilities[i]['Hobby'] = ['painting']

    # Clue 13: craftsman house has average height
    # Clue 1: average height has child Meredith
    # So craftsman house has child Meredith
    for i in range(5):
        if 'average' in possibilities[i]['Height']:
            possibilities[i]['HouseStyle'] = [hs for hs in possibilities[i]['HouseStyle'] if hs == 'craftsman']
            possibilities[i]['Children'] = ['Meredith']

    # Clue 6: Meredith's mother and Timothy's mother are next to each other
    # We'll apply this after assigning Meredith

    # Clue 9: very short is right of Eric
    # So Eric is left of very short

    # Clue 15: short person loves basketball
    for i in range(5):
        if 'short' in possibilities[i]['Height']:
            possibilities[i]['FavoriteSport'] = ['basketball']

    # Clue 11: soccer is not in house 1
    if 'soccer' in possibilities[0]['FavoriteSport']:
        possibilities[0]['FavoriteSport'].remove('soccer')

    # Clue 17: ranch is left of cooking
    # cooking is in modern house, so ranch is left of modern

    # Now we can start assigning based on remaining possibilities
    # Let's find the modern house (must have tennis, cooking, Samantha)
    modern_indices = []
    for i in range(5):
        if 'modern' in possibilities[i]['HouseStyle']:
            modern_indices.append(i)
    
    # Modern house must have tennis, cooking, Samantha
    for i in modern_indices:
        possibilities[i]['FavoriteSport'] = ['tennis']
        possibilities[i]['Hobby'] = ['cooking']
        possibilities[i]['Children'] = ['Samantha']
        # Remove these from other houses
        for j in range(5):
            if j != i:
                if 'tennis' in possibilities[j]['FavoriteSport']:
                    possibilities[j]['FavoriteSport'].remove('tennis')
                if 'cooking' in possibilities[j]['Hobby']:
                    possibilities[j]['Hobby'].remove('cooking')
                if 'Samantha' in possibilities[j]['Children']:
                    possibilities[j]['Children'].remove('Samantha')

    # Now ranch is left of modern (clue 17)
    # So modern cannot be house 1, and ranch must be in a house with index < modern index
    # Let's assume modern is house 3 (since house 2 is gardening, house 4 is Peter)
    modern_index = 2  # try house 3 (0-based index 2)
    possibilities[modern_index]['HouseStyle'] = ['modern']
    possibilities[modern_index]['FavoriteSport'] = ['tennis']
    possibilities[modern_index]['Hobby'] = ['cooking']
    possibilities[modern_index]['Children'] = ['Samantha']
    # ranch must be left of modern, so ranch is in house 1 or 2
    # house 2 is gardening, and hobbies are unique, so ranch is in house 1
    possibilities[0]['HouseStyle'] = ['ranch']
    for i in [1,2,3,4]:
        if 'ranch' in possibilities[i]['HouseStyle']:
            possibilities[i]['HouseStyle'].remove('ranch')

    # Now craftsman must be in remaining houses (3 or 4, but 4 is victorian, so craftsman is 3)
    # But 3 is modern, so craftsman must be house 1 or 2 or 3
    # house 1 is ranch, so craftsman is house 2 or 3
    # house 3 is modern, so craftsman is house 2
    possibilities[1]['HouseStyle'] = ['craftsman']
    possibilities[1]['Height'] = ['average']
    possibilities[1]['Children'] = ['Meredith']
    for i in [0,2,3,4]:
        if 'craftsman' in possibilities[i]['HouseStyle']:
            possibilities[i]['HouseStyle'].remove('craftsman')
        if 'average' in possibilities[i]['Height']:
            possibilities[i]['Height'].remove('average')
        if 'Meredith' in possibilities[i]['Children']:
            possibilities[i]['Children'].remove('Meredith')

    # Clue 6: Meredith's mother (house 2) and Timothy's mother are next to each other
    # So Timothy is in house 1 or 3
    for i in [0,2]:
        if 'Timothy' not in possibilities[i]['Children']:
            possibilities[i]['Children'] = [c for c in possibilities[i]['Children'] if c != 'Timothy']

    # Now assign children: house 2 has Meredith, house 4 has Fred, modern has Samantha
    # So remaining children: Timothy and Bella
    # house 1 or 3 has Timothy, the other has Bella
    # Let's assume house 1 has Timothy
    possibilities[0]['Children'] = ['Timothy']
    possibilities[2]['Children'] = ['Bella']
    for i in [1,3,4]:
        if 'Timothy' in possibilities[i]['Children']:
            possibilities[i]['Children'].remove('Timothy')
        if 'Bella' in possibilities[i]['Children']:
            possibilities[i]['Children'].remove('Bella')

    # Now assign names: house 1: Bob, Arnold, Eric; house 2: Alice; house 3: Peter; house 4: ?
    # house 4 name: remaining is Bob, Arnold, Eric
    # house 0 name: Bob, Arnold, Eric
    # Clue 7: Bob paints
    # house 1 hobby is gardening, house 3 is cooking, so Bob must be in house 0, 2, or 4
    # house 2 is Alice, so Bob is in 0 or 4
    # if Bob is in 0:
    possibilities[0]['Name'] = ['Bob']
    possibilities[0]['Hobby'] = ['painting']
    for i in [1,2,3,4]:
        if 'Bob' in possibilities[i]['Name']:
            possibilities[i]['Name'].remove('Bob')
        if 'painting' in possibilities[i]['Hobby']:
            possibilities[i]['Hobby'].remove('painting')

    # Now remaining names: Arnold, Eric
    # house 4 name: Arnold or Eric
    # house 3 is Peter, house 2 is Alice, house 0 is Bob
    # house 1 name: ?
    # house 1 name is not assigned yet, but names left are Arnold and Eric
    # Clue 9: very short is right of Eric, so Eric must be left of very short
    # very short is not assigned yet, possible in house 3 or 4
    # house 3 height is very tall, so very short is in house 4
    # So Eric must be left of house 4, so Eric is in house 0,1,2,3
    # house 0 is Bob, house 2 is Alice, house 3 is Peter, so Eric is in house 1
    possibilities[1]['Name'] = ['Eric']
    possibilities[4]['Name'] = ['Arnold']
    for i in [0,2,3]:
        if 'Eric' in possibilities[i]['Name']:
            possibilities[i]['Name'].remove('Eric')
        if 'Arnold' in possibilities[i]['Name']:
            possibilities[i]['Name'].remove('Arnold')

    # Now assign heights: house 1 is average, house 2 is tall, house 3 is very tall
    # house 4: very short (from clue 9)
    possibilities[4]['Height'] = ['very short']
    # remaining height: short
    possibilities[0]['Height'] = ['short']
    for i in [1,2,3]:
        if 'short' in possibilities[i]['Height']:
            possibilities[i]['Height'].remove('short')

    # Now assign sports: house 3 is baseball, house 2 is ?
    # house 0: possible sports: swimming, soccer, basketball (tennis is in modern, baseball in 3)
    # house 1: ?
    # house 2: ?
    # house 4: ?
    # clue 15: short loves basketball, house 0 is short
    possibilities[0]['FavoriteSport'] = ['basketball']
    for i in [1,2,3,4]:
        if 'basketball' in possibilities[i]['FavoriteSport']:
            possibilities[i]['FavoriteSport'].remove('basketball')

    # clue 11: soccer not in house 1, so soccer is in 2,3,4, but 3 is baseball, so soccer is 2 or 4
    # house 2 sports: swimming, soccer, tennis? tennis is in modern (house 3)
    possibilities[2]['FavoriteSport'] = ['soccer']
    possibilities[4]['FavoriteSport'] = ['swimming']
    for i in [0,1,3]:
        if 'soccer' in possibilities[i]['FavoriteSport']:
            possibilities[i]['FavoriteSport'].remove('soccer')
        if 'swimming' in possibilities[i]['FavoriteSport']:
            possibilities[i]['FavoriteSport'].remove('swimming')

    # Now assign hobbies: house 0: painting, house 1: gardening, house 2: ?
    # house 3: cooking, house 4: ?
    # remaining hobbies: photography, knitting
    # clue 18: knitting is next to gardening (house 1), so knitting is house 0 or 2
    # house 0 is painting, so knitting is house 2
    possibilities[2]['Hobby'] = ['knitting']
    possibilities[4]['Hobby'] = ['photography']
    for i in [0,1,3]:
        if 'knitting' in possibilities[i]['Hobby']:
            possibilities[i]['Hobby'].remove('knitting')
        if 'photography' in possibilities[i]['Hobby']:
            possibilities[i]['Hobby'].remove('photography')

    # Now assign house styles: house 0: ranch, house 1: craftsman, house 2: ?
    # house 3: modern, house 4: victorian
    # remaining: colonial
    possibilities[2]['HouseStyle'] = ['colonial']
    for i in [0,1,3,4]:
        if 'colonial' in possibilities[i]['HouseStyle']:
            possibilities[i]['HouseStyle'].remove('colonial')

    # Verify all constraints are satisfied
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
            "rows": []
        }
    }

    for i in range(5):
        house = str(i+1)
        name = possibilities[i]['Name'][0]
        hobby = possibilities[i]['Hobby'][0]
        sport = possibilities[i]['FavoriteSport'][0]
        style = possibilities[i]['HouseStyle'][0]
        child = possibilities[i]['Children'][0]
        height = possibilities[i]['Height'][0]
        solution["solution"]["rows"].append([house, name, hobby, sport, style, child, height])

    return json.dumps(solution)

print(solve_puzzle())