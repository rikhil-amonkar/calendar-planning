import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric']
    hobbies = ['cooking', 'gardening', 'painting', 'photography', 'knitting']
    sports = ['swimming', 'tennis', 'soccer', 'baseball', 'basketball']
    styles = ['ranch', 'craftsman', 'victorian', 'modern', 'colonial']
    children = ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred']
    heights = ['average', 'very tall', 'very short', 'short', 'tall']

    all_permutations = list(itertools.permutations(range(5)))

    for name_order in all_permutations:
        for hobby_order in all_permutations:
            for sport_order in all_permutations:
                for style_order in all_permutations:
                    for child_order in all_permutations:
                        for height_order in all_permutations:
                            # Assign values based on current permutation
                            name_map = {name: i + 1 for i, name in enumerate(names)}
                            hobby_map = {hobby: i + 1 for i, hobby in enumerate(hobbies)}
                            sport_map = {sport: i + 1 for i, sport in enumerate(sports)}
                            style_map = {style: i + 1 for i, style in enumerate(styles)}
                            child_map = {child: i + 1 for i, child in enumerate(children)}
                            height_map = {height: i + 1 for i, height in enumerate(heights)}

                            name_positions = {names[i]: house for i, house in enumerate(name_order)}
                            hobby_positions = {hobbies[i]: house for i, house in enumerate(hobby_order)}
                            sport_positions = {sports[i]: house for i, house in enumerate(sport_order)}
                            style_positions = {styles[i]: house for i, house in enumerate(style_order)}
                            child_positions = {children[i]: house for i, house in enumerate(child_order)}
                            height_positions = {heights[i]: house for i, house in enumerate(height_order)}

                            # Check clues
                            if (height_positions['average'] == child_positions['Meredith'] and
                                height_positions['tall'] == 2 and
                                name_positions['Peter'] + 1 == style_positions['victorian'] and
                                name_positions['Alice'] == height_positions['tall'] and
                                sport_positions['baseball'] == height_positions['very tall'] and
                                abs(child_positions['Meredith'] - child_positions['Timothy']) == 1 and
                                name_positions['Bob'] == hobby_positions['painting'] and
                                hobby_positions['gardening'] == 2 and
                                height_positions['very short'] > name_positions['Eric'] and
                                sport_positions['tennis'] == child_positions['Samantha'] and
                                sport_positions['soccer'] != 1 and
                                child_positions['Samantha'] == style_positions['modern'] and
                                style_positions['craftsman'] == height_positions['average'] and
                                child_positions['Fred'] == style_positions['victorian'] and
                                height_positions['short'] == sport_positions['basketball'] and
                                name_positions['Peter'] == height_positions['very tall'] and
                                style_positions['ranch'] < hobby_positions['cooking'] and
                                abs(hobby_positions['knitting'] - hobby_positions['gardening']) == 1 and
                                style_positions['modern'] == hobby_positions['cooking'] and
                                style_positions['victorian'] == 5):
                                
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
                                        "rows": []
                                    }
                                }

                                for house in houses:
                                    name = names[name_order[house - 1]]
                                    hobby = hobbies[hobby_order[house - 1]]
                                    sport = sports[sport_order[house - 1]]
                                    style = styles[style_order[house - 1]]
                                    child = children[child_order[house - 1]]
                                    height = heights[height_order[house - 1]]
                                    solution["solution"]["rows"].append([str(house), name, hobby, sport, style, child, height])

                                return json.dumps(solution, indent=2)

print(solve_puzzle())