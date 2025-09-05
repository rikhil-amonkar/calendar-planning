import json
from copy import deepcopy

def solve_puzzle():
    houses = [1, 2, 3, 4]

    Names = ['Peter', 'Eric', 'Alice', 'Arnold']
    Educations = ['bachelor', 'high school', 'associate', 'master']
    MusicGenres = ['jazz', 'rock', 'pop', 'classical']
    Colors = ['green', 'red', 'yellow', 'white']
    Flowers = ['lilies', 'carnations', 'daffodils', 'roses']

    # Initialize remaining values
    names_left = set(Names)
    educ_left = set(Educations)
    music_left = set(MusicGenres)
    color_left = set(Colors)
    flower_left = set(Flowers)

    # Assignments per house index 1..4
    assignments = {i: {'Name': None, 'Education': None, 'MusicGenre': None, 'Color': None, 'Flower': None} for i in houses}

    # Requirements that certain attributes must be at specific houses due to "directly left of" constraints
    # Structure: {house_index: {'Name': val?, 'Education': val?, 'MusicGenre': val?, 'Color': val?, 'Flower': val?}}
    required_at = {}

    def check_required(i, candidate, req_at):
        reqs = req_at.get(i, {})
        for key, val in reqs.items():
            if candidate[key] is not None and candidate[key] != val:
                return False
        return True

    def add_requirement(req_at, house, key, val):
        if house not in (1, 2, 3, 4):
            return False
        if house not in req_at:
            req_at[house] = {}
        if key in req_at[house] and req_at[house][key] != val:
            return False
        req_at[house][key] = val
        return True

    def backtrack(i, names_left, educ_left, music_left, color_left, flower_left, assignments, required_at):
        if i == 5:
            # All houses assigned
            return assignments

        # Prepare loops over remaining values
        for name in list(names_left):
            # Name positional constraints
            if i == 2 and name == 'Eric':
                continue
            if i == 3 and name == 'Arnold':
                continue

            for edu in list(educ_left):
                # Alice <-> master
                if (name == 'Alice') != (edu == 'master'):
                    continue
                # Associate not in house 4
                if i == 4 and edu == 'associate':
                    continue

                for music in list(music_left):
                    # Pop only in house 2
                    if (i == 2 and music != 'pop') or (i != 2 and music == 'pop'):
                        continue

                    for color in list(color_left):
                        # Red <-> Rock
                        if (color == 'red') != (music == 'rock'):
                            continue
                        # Arnold <-> Yellow
                        if (name == 'Arnold') != (color == 'yellow'):
                            continue

                        for flower in list(flower_left):
                            # Carnations not in house 1 or 4
                            if flower == 'carnations' and i in (1, 4):
                                continue
                            # Bachelor <-> Daffodils and Daffodils <-> Yellow (thus Bachelor <-> Yellow)
                            # Implement as chained equivalences:
                            # edu == 'bachelor' iff flower == 'daffodils'
                            if (edu == 'bachelor') != (flower == 'daffodils'):
                                continue
                            # color yellow iff (edu bachelor and flower daffodils) already partially ensured by name/color link,
                            # but enforce fully:
                            if (color == 'yellow') != (edu == 'bachelor' and flower == 'daffodils'):
                                continue

                            # House edge constraints for adjacency requirements
                            # Master must have right neighbor (i < 4)
                            if edu == 'master' and i == 4:
                                continue
                            # Red must have right neighbor (white)
                            if color == 'red' and i == 4:
                                continue
                            # Yellow must have right neighbor (roses)
                            if color == 'yellow' and i == 4:
                                continue
                            # Classical must have left neighbor master
                            if music == 'classical' and i == 1:
                                continue
                            # White must have left neighbor red
                            if color == 'white' and i == 1:
                                continue

                            candidate = {
                                'Name': name,
                                'Education': edu,
                                'MusicGenre': music,
                                'Color': color,
                                'Flower': flower
                            }

                            # Check required_at for this house
                            if not check_required(i, candidate, required_at):
                                continue

                            # Check left neighbor inverse constraints (since left is already assigned)
                            if i > 1:
                                left = assignments[i - 1]
                                # If current is classical, left must be master
                                if music == 'classical' and left['Education'] != 'master':
                                    continue
                                # If current color is white, left must be red
                                if color == 'white' and left['Color'] != 'red':
                                    continue
                                # If current flower is roses, left must be yellow
                                if flower == 'roses' and left['Color'] != 'yellow':
                                    continue
                                # Also ensure that if left was master, current must be classical
                                if left['Education'] == 'master' and music != 'classical':
                                    continue
                                # If left was red, current must be white
                                if left['Color'] == 'red' and color != 'white':
                                    continue
                                # If left was yellow, current must be roses
                                if left['Color'] == 'yellow' and flower != 'roses':
                                    continue

                            # After all checks, assign and propagate requirements to the right neighbor
                            new_required = {h: req.copy() for h, req in required_at.items()}

                            # Propagate "directly left of" constraints to i+1
                            if i < 4:
                                # Master -> next is classical music
                                if edu == 'master':
                                    if not add_requirement(new_required, i + 1, 'MusicGenre', 'classical'):
                                        continue
                                    # Ensure 'classical' still available for future
                                    if 'classical' not in music_left or (i == 2 and 'classical' == 'pop'):
                                        # also ensure it wasn't already used earlier
                                        pass
                                # Red -> next is white color
                                if color == 'red':
                                    if not add_requirement(new_required, i + 1, 'Color', 'white'):
                                        continue
                                # Yellow -> next has roses flower
                                if color == 'yellow':
                                    if not add_requirement(new_required, i + 1, 'Flower', 'roses'):
                                        continue

                            # Also ensure required future values are still available in remaining domains after we remove current
                            # Build temporary remaining sets
                            t_names_left = set(names_left)
                            t_educ_left = set(educ_left)
                            t_music_left = set(music_left)
                            t_color_left = set(color_left)
                            t_flower_left = set(flower_left)

                            # Remove chosen values
                            t_names_left.remove(name)
                            t_educ_left.remove(edu)
                            t_music_left.remove(music)
                            t_color_left.remove(color)
                            t_flower_left.remove(flower)

                            # Quick forward-check: for any requirement at i+1 for a value, ensure it's still in remaining set
                            if i < 4 and (i + 1) in new_required:
                                req_next = new_required[i + 1]
                                if 'Name' in req_next and req_next['Name'] not in t_names_left:
                                    continue
                                if 'Education' in req_next and req_next['Education'] not in t_educ_left:
                                    continue
                                if 'MusicGenre' in req_next and req_next['MusicGenre'] not in t_music_left:
                                    continue
                                if 'Color' in req_next and req_next['Color'] not in t_color_left:
                                    continue
                                if 'Flower' in req_next and req_next['Flower'] not in t_flower_left:
                                    continue

                            # Commit assignment
                            assignments[i] = candidate

                            result = backtrack(
                                i + 1,
                                t_names_left,
                                t_educ_left,
                                t_music_left,
                                t_color_left,
                                t_flower_left,
                                assignments,
                                new_required
                            )
                            if result is not None:
                                return result

                            # Undo handled by backtracking loop

        return None

    solution = backtrack(
        1,
        names_left,
        educ_left,
        music_left,
        color_left,
        flower_left,
        assignments,
        required_at
    )
    return solution

def main():
    solution = solve_puzzle()
    if solution is None:
        output = {
            "solution": {
                "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                "rows": []
            }
        }
    else:
        rows = []
        for i in [1, 2, 3, 4]:
            row = [
                str(i),
                solution[i]['Name'],
                solution[i]['Education'],
                solution[i]['MusicGenre'],
                solution[i]['Color'],
                solution[i]['Flower']
            ]
            rows.append(row)
        output = {
            "solution": {
                "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                "rows": rows
            }
        }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()