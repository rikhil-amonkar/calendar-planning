import json
import copy

def main():
    # Define the categories and their possible values
    categories = {
        'names': ['Alice', 'Peter', 'Eric', 'Bob', 'Arnold', 'Carol'],
        'cigars': ['pall mall', 'yellow monster', 'dunhill', 'blue master', 'prince', 'blends'],
        'music': ['hip hop', 'jazz', 'country', 'pop', 'classical', 'rock'],
        'drinks': ['water', 'milk', 'boba tea', 'tea', 'root beer', 'coffee'],
        'mothers': ['Kailyn', 'Penny', 'Janelle', 'Holly', 'Sarah', 'Aniya'],
        'foods': ['soup', 'pizza', 'spaghetti', 'stir fry', 'stew', 'grilled cheese']
    }
    
    # Initialize the domains for each attribute to all houses (1-6)
    domains = {}
    for category in categories.values():
        for attribute in category:
            domains[attribute] = set(range(1, 7))
    
    # Define constraint functions for each clue
    def constraint2(domains):
        # Eric is not in the second house.
        old = domains['Eric'].copy()
        domains['Eric'] -= {2}
        return old != domains['Eric']
    
    def constraint5(domains):
        # Eric is directly left of Carol.
        changed = False
        eric_dom = domains['Eric']
        carol_dom = domains['Carol']
        new_eric = set()
        for e in eric_dom:
            if e + 1 in carol_dom:
                new_eric.add(e)
        if new_eric != eric_dom:
            domains['Eric'] = new_eric
            changed = True
        new_carol = set()
        for c in carol_dom:
            if c - 1 in eric_dom:
                new_carol.add(c)
        if new_carol != carol_dom:
            domains['Carol'] = new_carol
            changed = True
        return changed
    
    def constraint1(domains):
        # Carol is directly left of the person who loves eating grilled cheese.
        changed = False
        carol_dom = domains['Carol']
        grill_dom = domains['grilled cheese']
        new_carol = set()
        for c in carol_dom:
            if c + 1 in grill_dom:
                new_carol.add(c)
        if new_carol != carol_dom:
            domains['Carol'] = new_carol
            changed = True
        new_grill = set()
        for g in grill_dom:
            if g - 1 in carol_dom:
                new_grill.add(g)
        if new_grill != grill_dom:
            domains['grilled cheese'] = new_grill
            changed = True
        return changed
    
    def constraint3(domains):
        # The person whose mother's name is Holly is somewhere to the right of Carol.
        changed = False
        holly_dom = domains['Holly']
        carol_dom = domains['Carol']
        new_holly = {h for h in holly_dom if any(h > c for c in carol_dom)}
        if new_holly != holly_dom:
            domains['Holly'] = new_holly
            changed = True
        new_carol = {c for c in carol_dom if any(c < h for h in holly_dom)}
        if new_carol != carol_dom:
            domains['Carol'] = new_carol
            changed = True
        return changed
    
    def constraint4(domains):
        # The person who loves eating grilled cheese is somewhere to the right of the person who loves rock music.
        changed = False
        grill_dom = domains['grilled cheese']
        rock_dom = domains['rock']
        new_grill = {g for g in grill_dom if any(g > r for r in rock_dom)}
        if new_grill != grill_dom:
            domains['grilled cheese'] = new_grill
            changed = True
        new_rock = {r for r in rock_dom if any(r < g for g in grill_dom)}
        if new_rock != rock_dom:
            domains['rock'] = new_rock
            changed = True
        return changed
    
    def constraint6(domains):
        # The person who loves pop music is not in the third house.
        old = domains['pop'].copy()
        domains['pop'] -= {3}
        return old != domains['pop']
    
    def constraint7(domains):
        # Eric is the person who loves country music.
        changed = False
        eric_dom = domains['Eric']
        country_dom = domains['country']
        intersection = eric_dom & country_dom
        if eric_dom != intersection:
            domains['Eric'] = intersection
            changed = True
        if country_dom != intersection:
            domains['country'] = intersection
            changed = True
        return changed
    
    def constraint8(domains):
        # The person who loves classical music is in the sixth house.
        old = domains['classical'].copy()
        domains['classical'] = {6}
        return old != domains['classical']
    
    def constraint9(domains):
        # The coffee drinker is Bob.
        changed = False
        bob_dom = domains['Bob']
        coffee_dom = domains['coffee']
        intersection = bob_dom & coffee_dom
        if bob_dom != intersection:
            domains['Bob'] = intersection
            changed = True
        if coffee_dom != intersection:
            domains['coffee'] = intersection
            changed = True
        return changed
    
    def constraint10(domains):
        # The person who smokes many unique blends is Peter.
        changed = False
        peter_dom = domains['Peter']
        blends_dom = domains['blends']
        intersection = peter_dom & blends_dom
        if peter_dom != intersection:
            domains['Peter'] = intersection
            changed = True
        if blends_dom != intersection:
            domains['blends'] = intersection
            changed = True
        return changed
    
    def constraint11(domains):
        # The person who loves the stew is not in the fifth house.
        old = domains['stew'].copy()
        domains['stew'] -= {5}
        return old != domains['stew']
    
    def constraint12(domains):
        # The root beer lover is directly left of The person whose mother's name is Janelle.
        changed = False
        rootbeer_dom = domains['root beer']
        janelle_dom = domains['Janelle']
        new_rootbeer = set()
        for r in rootbeer_dom:
            if r + 1 in janelle_dom:
                new_rootbeer.add(r)
        if new_rootbeer != rootbeer_dom:
            domains['root beer'] = new_rootbeer
            changed = True
        new_janelle = set()
        for j in janelle_dom:
            if j - 1 in rootbeer_dom:
                new_janelle.add(j)
        if new_janelle != janelle_dom:
            domains['Janelle'] = new_janelle
            changed = True
        return changed
    
    def constraint13(domains):
        # There are two houses between The person whose mother's name is Sarah and the person who smokes Yellow Monster.
        changed = False
        sarah_dom = domains['Sarah']
        yellow_dom = domains['yellow monster']
        new_sarah = set()
        for s in sarah_dom:
            if (s - 3 in yellow_dom) or (s + 3 in yellow_dom):
                new_sarah.add(s)
        if new_sarah != sarah_dom:
            domains['Sarah'] = new_sarah
            changed = True
        new_yellow = set()
        for y in yellow_dom:
            if (y - 3 in sarah_dom) or (y + 3 in sarah_dom):
                new_yellow.add(y)
        if new_yellow != yellow_dom:
            domains['yellow monster'] = new_yellow
            changed = True
        return changed
    
    def constraint14(domains):
        # Eric is the tea drinker.
        changed = False
        eric_dom = domains['Eric']
        tea_dom = domains['tea']
        intersection = eric_dom & tea_dom
        if eric_dom != intersection:
            domains['Eric'] = intersection
            changed = True
        if tea_dom != intersection:
            domains['tea'] = intersection
            changed = True
        return changed
    
    def constraint15(domains):
        # The person partial to Pall Mall is somewhere to the right of the person who loves stir fry.
        changed = False
        pall_dom = domains['pall mall']
        stirfry_dom = domains['stir fry']
        new_pall = {p for p in pall_dom if any(p > s for s in stirfry_dom)}
        if new_pall != pall_dom:
            domains['pall mall'] = new_pall
            changed = True
        new_stirfry = {s for s in stirfry_dom if any(s < p for p in pall_dom)}
        if new_stirfry != stirfry_dom:
            domains['stir fry'] = new_stirfry
            changed = True
        return changed
    
    def constraint16(domains):
        # The person who loves the soup is Bob.
        changed = False
        bob_dom = domains['Bob']
        soup_dom = domains['soup']
        intersection = bob_dom & soup_dom
        if bob_dom != intersection:
            domains['Bob'] = intersection
            changed = True
        if soup_dom != intersection:
            domains['soup'] = intersection
            changed = True
        return changed
    
    def constraint17(domains):
        # The person who loves hip-hop music is directly left of The person whose mother's name is Kailyn.
        changed = False
        hiphop_dom = domains['hip hop']
        kailyn_dom = domains['Kailyn']
        new_hiphop = set()
        for h in hiphop_dom:
            if h + 1 in kailyn_dom:
                new_hiphop.add(h)
        if new_hiphop != hiphop_dom:
            domains['hip hop'] = new_hiphop
            changed = True
        new_kailyn = set()
        for k in kailyn_dom:
            if k - 1 in hiphop_dom:
                new_kailyn.add(k)
        if new_kailyn != kailyn_dom:
            domains['Kailyn'] = new_kailyn
            changed = True
        return changed
    
    def constraint18(domains):
        # Arnold is somewhere to the right of The person whose mother's name is Kailyn.
        changed = False
        arnold_dom = domains['Arnold']
        kailyn_dom = domains['Kailyn']
        new_arnold = {a for a in arnold_dom if any(a > k for k in kailyn_dom)}
        if new_arnold != arnold_dom:
            domains['Arnold'] = new_arnold
            changed = True
        new_kailyn = {k for k in kailyn_dom if any(k < a for a in arnold_dom)}
        if new_kailyn != kailyn_dom:
            domains['Kailyn'] = new_kailyn
            changed = True
        return changed
    
    def constraint19(domains):
        # The one who only drinks water is directly left of the person who smokes Blue Master.
        changed = False
        water_dom = domains['water']
        blue_dom = domains['blue master']
        new_water = set()
        for w in water_dom:
            if w + 1 in blue_dom:
                new_water.add(w)
        if new_water != water_dom:
            domains['water'] = new_water
            changed = True
        new_blue = set()
        for b in blue_dom:
            if b - 1 in water_dom:
                new_blue.add(b)
        if new_blue != blue_dom:
            domains['blue master'] = new_blue
            changed = True
        return changed
    
    def constraint20(domains):
        # The person who loves the spaghetti eater is somewhere to the left of the person who smokes many unique blends.
        changed = False
        spaghetti_dom = domains['spaghetti']
        blends_dom = domains['blends']
        new_spaghetti = {s for s in spaghetti_dom if any(s < b for b in blends_dom)}
        if new_spaghetti != spaghetti_dom:
            domains['spaghetti'] = new_spaghetti
            changed = True
        new_blends = {b for b in blends_dom if any(b > s for s in spaghetti_dom)}
        if new_blends != blends_dom:
            domains['blends'] = new_blends
            changed = True
        return changed
    
    def constraint21(domains):
        # The person whose mother's name is Sarah is directly left of the person who loves jazz music.
        changed = False
        sarah_dom = domains['Sarah']
        jazz_dom = domains['jazz']
        new_sarah = set()
        for s in sarah_dom:
            if s + 1 in jazz_dom:
                new_sarah.add(s)
        if new_sarah != sarah_dom:
            domains['Sarah'] = new_sarah
            changed = True
        new_jazz = set()
        for j in jazz_dom:
            if j - 1 in sarah_dom:
                new_jazz.add(j)
        if new_jazz != jazz_dom:
            domains['jazz'] = new_jazz
            changed = True
        return changed
    
    def constraint22(domains):
        # The person who loves hip-hop music is directly left of the root beer lover.
        changed = False
        hiphop_dom = domains['hip hop']
        rootbeer_dom = domains['root beer']
        new_hiphop = set()
        for h in hiphop_dom:
            if h + 1 in rootbeer_dom:
                new_hiphop.add(h)
        if new_hiphop != hiphop_dom:
            domains['hip hop'] = new_hiphop
            changed = True
        new_rootbeer = set()
        for r in rootbeer_dom:
            if r - 1 in hiphop_dom:
                new_rootbeer.add(r)
        if new_rootbeer != rootbeer_dom:
            domains['root beer'] = new_rootbeer
            changed = True
        return changed
    
    def constraint23(domains):
        # The one who only drinks water is the person who loves the stew.
        changed = False
        water_dom = domains['water']
        stew_dom = domains['stew']
        intersection = water_dom & stew_dom
        if water_dom != intersection:
            domains['water'] = intersection
            changed = True
        if stew_dom != intersection:
            domains['stew'] = intersection
            changed = True
        return changed
    
    def constraint24(domains):
        # The Dunhill smoker is not in the second house.
        old = domains['dunhill'].copy()
        domains['dunhill'] -= {2}
        return old != domains['dunhill']
    
    def constraint25(domains):
        # The person who likes milk is The person whose mother's name is Janelle.
        changed = False
        milk_dom = domains['milk']
        janelle_dom = domains['Janelle']
        intersection = milk_dom & janelle_dom
        if milk_dom != intersection:
            domains['milk'] = intersection
            changed = True
        if janelle_dom != intersection:
            domains['Janelle'] = intersection
            changed = True
        return changed
    
    def constraint26(domains):
        # Eric is The person whose mother's name is Aniya.
        changed = False
        eric_dom = domains['Eric']
        aniya_dom = domains['Aniya']
        intersection = eric_dom & aniya_dom
        if eric_dom != intersection:
            domains['Eric'] = intersection
            changed = True
        if aniya_dom != intersection:
            domains['Aniya'] = intersection
            changed = True
        return changed

    # List of constraint functions
    constraints = [
        constraint2, constraint5, constraint1, constraint3, constraint4,
        constraint6, constraint7, constraint8, constraint9, constraint10,
        constraint11, constraint12, constraint13, constraint14, constraint15,
        constraint16, constraint17, constraint18, constraint19, constraint20,
        constraint21, constraint22, constraint23, constraint24, constraint25,
        constraint26
    ]
    
    # Function to enforce all-different for a category
    def all_different(domains, attributes):
        changed = False
        for attr in attributes:
            if len(domains[attr]) == 1:
                value = next(iter(domains[attr]))
                for other in attributes:
                    if other != attr and value in domains[other]:
                        domains[other].remove(value)
                        changed = True
        return changed

    # Constraint propagation function
    def propagate(domains):
        changed = True
        while changed:
            changed = False
            for constraint in constraints:
                if constraint(domains):
                    changed = True
            for category in categories.values():
                if all_different(domains, category):
                    changed = True
        return domains

    # Backtracking search with forward checking
    def backtrack(assignment, domains):
        # If all domains are singletons, build complete assignment
        if all(len(domains[attr]) == 1 for attr in domains):
            complete_assignment = assignment.copy()
            for attr in domains:
                if attr not in complete_assignment:
                    complete_assignment[attr] = next(iter(domains[attr]))
            return complete_assignment

        # Select unassigned variable with minimum remaining values
        unassigned = [attr for attr in domains if len(domains[attr]) > 1]
        if not unassigned:
            return None  # No solution
        attr = min(unassigned, key=lambda a: len(domains[a]))

        for value in list(domains[attr]):
            new_domains = copy.deepcopy(domains)
            new_domains[attr] = {value}
            new_domains = propagate(new_domains)

            # Check for consistency
            if any(len(new_domains[a]) == 0 for a in new_domains):
                continue  # Skip inconsistent assignment

            # Update assignment
            new_assignment = assignment.copy()
            new_assignment[attr] = value

            # Recursive call
            result = backtrack(new_assignment, new_domains)
            if result is not None:
                return result

        return None

    # Initial propagation
    domains = propagate(domains)

    # Check if solved
    if all(len(domains[attr]) == 1 for attr in domains):
        assignment = {attr: next(iter(domains[attr])) for attr in domains}
    else:
        assignment = backtrack({}, domains)
        if assignment is None:
            raise Exception("No solution found")

    # Build the solution table
    houses = [{} for _ in range(6)]
    for category_name, attributes in categories.items():
        for attr in attributes:
            house_num = assignment[attr]
            houses[house_num-1][category_name] = attr
    
    # Map to output format
    output_rows = []
    for i, house in enumerate(houses):
        output_rows.append([
            str(i+1),
            house['names'],
            house['cigars'],
            house['music'],
            house['drinks'],
            house['mothers'],
            house['foods']
        ])
    
    # Create the solution dictionary
    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
            "rows": output_rows
        }
    }
    
    # Output as JSON
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()