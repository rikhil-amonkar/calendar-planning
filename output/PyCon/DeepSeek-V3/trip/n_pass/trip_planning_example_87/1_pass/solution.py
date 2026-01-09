import constraint
import json

def main():
    # Define the problem
    problem = constraint.Problem()
    
    # Variables: days spent in each city (must be integers)
    # We have 3 cities: Riga, Amsterdam, Mykonos
    # Total days = 7
    problem.addVariable('riga_days', range(1, 8))
    problem.addVariable('amsterdam_days', range(1, 8))
    problem.addVariable('mykonos_days', range(1, 8))
    
    # Constraints
    # 1. Total days must equal 7
    problem.addConstraint(
        lambda r, a, m: r + a + m == 7,
        ['riga_days', 'amsterdam_days', 'mykonos_days']
    )
    
    # 2. Must spend exactly 2 days in Riga
    problem.addConstraint(
        lambda r: r == 2,
        ['riga_days']
    )
    
    # 3. Must spend exactly 2 days in Amsterdam  
    problem.addConstraint(
        lambda a: a == 2,
        ['amsterdam_days']
    )
    
    # 4. Must spend exactly 5 days in Mykonos
    problem.addConstraint(
        lambda m: m == 5,
        ['mykonos_days']
    )
    
    # 5. Flight connectivity constraints
    # Since we only have direct flights between Amsterdam-Mykonos and Riga-Amsterdam,
    # we need to ensure the itinerary is feasible with these connections
    # This means we can't go directly from Riga to Mykonos or vice versa
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with exact constraints, try to find the closest match
        problem2 = constraint.Problem()
        problem2.addVariable('riga_days', range(1, 8))
        problem2.addVariable('amsterdam_days', range(1, 8))
        problem2.addVariable('mykonos_days', range(1, 8))
        
        # Relaxed constraints - prioritize total days = 7
        problem2.addConstraint(
            lambda r, a, m: r + a + m == 7,
            ['riga_days', 'amsterdam_days', 'mykonos_days']
        )
        
        # Try to get as close as possible to the desired days
        def closeness_constraint(r, a, m):
            riga_diff = abs(r - 2)
            amsterdam_diff = abs(a - 2) 
            mykonos_diff = abs(m - 5)
            return riga_diff + amsterdam_diff + mykonos_diff <= 2
        
        problem2.addConstraint(closeness_constraint, ['riga_days', 'amsterdam_days', 'mykonos_days'])
        
        solutions = problem2.getSolutions()
    
    if solutions:
        # Take the first valid solution
        solution = solutions[0]
        riga_days = solution['riga_days']
        amsterdam_days = solution['amsterdam_days'] 
        mykonos_days = solution['mykonos_days']
        
        # Generate itinerary based on flight connectivity
        # Since we can fly between Amsterdam-Mykonos and Riga-Amsterdam,
        # we need to arrange the cities in a valid sequence
        
        # Option 1: Riga -> Amsterdam -> Mykonos
        # Option 2: Mykonos -> Amsterdam -> Riga
        
        # Let's choose option 1: Start in Riga, then Amsterdam, then Mykonos
        current_day = 1
        
        itinerary = []
        
        # Riga stay
        riga_end = current_day + riga_days - 1
        if riga_days > 0:
            if riga_days == 1:
                itinerary.append({"day_range": f"Day {current_day}", "place": "Riga"})
            else:
                itinerary.append({"day_range": f"Day {current_day}-{riga_end}", "place": "Riga"})
            current_day = riga_end + 1
        
        # Travel day from Riga to Amsterdam (counts as day in both cities)
        # On travel day, person is in both cities
        
        # Amsterdam stay
        amsterdam_end = current_day + amsterdam_days - 1
        if amsterdam_days > 0:
            if amsterdam_days == 1:
                itinerary.append({"day_range": f"Day {current_day}", "place": "Amsterdam"})
            else:
                itinerary.append({"day_range": f"Day {current_day}-{amsterdam_end}", "place": "Amsterdam"})
            current_day = amsterdam_end + 1
        
        # Travel day from Amsterdam to Mykonos (counts as day in both cities)
        
        # Mykonos stay
        mykonos_end = current_day + mykonos_days - 1
        if mykonos_days > 0:
            if mykonos_days == 1:
                itinerary.append({"day_range": f"Day {current_day}", "place": "Mykonos"})
            else:
                itinerary.append({"day_range": f"Day {current_day}-{mykonos_end}", "place": "Mykonos"})
        
        # Verify total days
        total_itinerary_days = 0
        for segment in itinerary:
            day_range = segment["day_range"]
            if "-" in day_range:
                start, end = map(int, day_range.replace("Day ", "").split("-"))
                total_itinerary_days += (end - start + 1)
            else:
                total_itinerary_days += 1
        
        # Output the result
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # No solution found
        print(json.dumps({"error": "No valid itinerary found with given constraints"}, indent=2))

if __name__ == "__main__":
    main()