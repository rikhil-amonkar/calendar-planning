from z3 import *
import json

def main():
    # Define city names and their IDs
    cities = ['Geneva', 'Istanbul', 'Vienna', 'Riga', 'Brussels', 'Madrid', 'Vilnius', 'Venice', 'Munich', 'Reykjavik']
    id_to_name = {i: name for i, name in enumerate(cities)}
    name_to_id = {name: i for i, name in enumerate(cities)}
    
    # Required days per city (by ID)
    days_req_by_id = [4, 4, 4, 2, 2, 4, 4, 5, 5, 2]
    req_minus_one = [d - 1 for d in days_req_by_id]  # Days minus one for each city
    
    # Build the set of directed flight edges
    bidirectional_phrases = [
        "Munich and Vienna", 
        "Istanbul and Brussels", 
        "Vienna and Vilnius", 
        "Madrid and Munich", 
        "Venice and Brussels", 
        "Riga and Brussels", 
        "Geneva and Istanbul", 
        "Munich and Reykjavik", 
        "Vienna and Istanbul", 
        "Riga and Istanbul", 
        "Reykjavik and Vienna", 
        "Venice and Munich", 
        "Madrid and Venice", 
        "Vilnius and Istanbul", 
        "Venice and Vienna", 
        "Venice and Istanbul", 
        "Munich and Istanbul", 
        "Reykjavik and Brussels", 
        "Vilnius and Brussels", 
        "Madrid and Vienna", 
        "Vienna and Riga", 
        "Geneva and Vienna", 
        "Madrid and Brussels", 
        "Vienna and Brussels", 
        "Geneva and Brussels", 
        "Geneva and Madrid", 
        "Munich and Brussels", 
        "Madrid and Istanbul", 
        "Geneva and Munich"
    ]
    
    directed_phrases = [
        "from Reykjavik to Madrid",
        "from Riga to Munich",
        "from Vilnius to Munich",
        "from Riga to Vilnius"
    ]
    
    edges_id = set()
    for s in bidirectional_phrases:
        parts = s.split(' and ')
        if len(parts) == 2:
            A, B = parts[0].strip(), parts[1].strip()
            if A in name_to_id and B in name_to_id:
                idA, idB = name_to_id[A], name_to_id[B]
                edges_id.add((idA, idB))
                edges_id.add((idB, idA))
    for s in directed_phrases:
        parts = s.split()
        if len(parts) == 4 and parts[0] == 'from' and parts[2] == 'to':
            A, B = parts[1], parts[3]
            if A in name_to_id and B in name_to_id:
                idA, idB = name_to_id[A], name_to_id[B]
                edges_id.add((idA, idB))
    
    # Initialize Z3 solver
    s = Solver()
    
    # City order variables: city_vars[i] is the ID of the city at position i
    city_vars = [Int(f'c_{i}') for i in range(10)]
    # Start day for each city in the order
    start_day = [Int(f's_{i}') for i in range(10)]
    
    # Fixed constraints: first city Geneva (ID 0), last city Brussels (ID 4)
    s.add(city_vars[0] == 0)
    s.add(city_vars[9] == 4)
    s.add(Distinct(city_vars))
    
    # Flight constraints between consecutive cities
    for i in range(9):
        a, b = city_vars[i], city_vars[i+1]
        s.add(Or([And(a == idA, b == idB) for (idA, idB) in edges_id]))
    
    # Start day constraints
    s.add(start_day[0] == 1)
    for i in range(1, 10):
        # Create a conditional expression for req_minus_one value
        req_val = If(city_vars[i-1] == 0, req_minus_one[0],
                If(city_vars[i-1] == 1, req_minus_one[1],
                If(city_vars[i-1] == 2, req_minus_one[2],
                If(city_vars[i-1] == 3, req_minus_one[3],
                If(city_vars[i-1] == 4, req_minus_one[4],
                If(city_vars[i-1] == 5, req_minus_one[5],
                If(city_vars[i-1] == 6, req_minus_one[6],
                If(city_vars[i-1] == 7, req_minus_one[7],
                If(city_vars[i-1] == 8, req_minus_one[8],
                If(city_vars[i-1] == 9, req_minus_one[9], 0))))))))))
        s.add(start_day[i] == start_day[i-1] + req_val)
    
    # Venice constraint (ID 7 must start on day 7)
    venice_constraints = []
    for k in range(10):
        venice_constraints.append(And(city_vars[k] == 7, start_day[k] == 7))
    s.add(Or(venice_constraints))
    
    # Vilnius constraint (ID 6 must start between 17 and 23 inclusive)
    vilnius_constraints = []
    for k in range(10):
        vilnius_constraints.append(And(city_vars[k] == 6, start_day[k] >= 17, start_day[k] <= 23))
    s.add(Or(vilnius_constraints))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        city_assign = [m.evaluate(city_vars[i]).as_long() for i in range(10)]
        start_assign = [m.evaluate(start_day[i]).as_long() for i in range(10)]
        
        # Build itinerary by day
        itinerary_by_day = [[] for _ in range(27)]
        for i in range(10):
            city_id = city_assign[i]
            city_name = id_to_name[city_id]
            start = start_assign[i]
            end = start + days_req_by_id[city_id] - 1
            for d in range(start, end + 1):
                if 1 <= d <= 27:
                    itinerary_by_day[d-1].append(city_name)
        
        # Prepare JSON output
        itinerary_output = []
        for d in range(1, 28):
            places = sorted(itinerary_by_day[d-1])
            itinerary_output.append({"day": d, "place": places})
        
        result = {"itinerary": itinerary_output}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()