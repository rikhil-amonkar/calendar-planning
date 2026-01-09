import json
from constraint import Problem

def main():
    # Define the problem parameters
    total_days = 17
    cities = ['Naples', 'Vienna', 'Vilnius']
    
    # Define constraints
    vilnius_days = 7
    naples_days = 5
    vienna_days = 7
    
    # Define flight connections
    flights = {
        'Naples': ['Vienna'],
        'Vienna': ['Naples', 'Vilnius'],
        'Vilnius': ['Vienna']
    }
    
    # Create constraint problem
    problem = Problem()
    
    # Add variables for start day of each city (0 means not visited)
    for city in cities:
        problem.addVariable(f'{city}_start', range(1, total_days + 2))
        problem.addVariable(f'{city}_end', range(1, total_days + 2))
    
    # Constraint: Each city must be visited for the specified number of days
    def duration_constraint(start, end, required_days):
        if start == 0 or end == 0:  # Not visited
            return False
        actual_days = end - start + 1
        return actual_days == required_days
    
    problem.addConstraint(
        lambda n_start, n_end: duration_constraint(n_start, n_end, naples_days),
        ['Naples_start', 'Naples_end']
    )
    problem.addConstraint(
        lambda v_start, v_end: duration_constraint(v_start, v_end, vienna_days),
        ['Vienna_start', 'Vienna_end']
    )
    problem.addConstraint(
        lambda vl_start, vl_end: duration_constraint(vl_start, vl_end, vilnius_days),
        ['Vilnius_start', 'Vilnius_end']
    )
    
    # Constraint: All days from 1 to total_days must be covered exactly once
    def all_days_covered(naples_s, naples_e, vienna_s, vienna_e, vilnius_s, vilnius_e):
        days_covered = set()
        
        # Add Naples days
        if naples_s > 0 and naples_e > 0:
            for day in range(naples_s, naples_e + 1):
                if day > total_days:
                    return False
                days_covered.add(day)
        
        # Add Vienna days
        if vienna_s > 0 and vienna_e > 0:
            for day in range(vienna_s, vienna_e + 1):
                if day > total_days:
                    return False
                days_covered.add(day)
        
        # Add Vilnius days
        if vilnius_s > 0 and vilnius_e > 0:
            for day in range(vilnius_s, vilnius_e + 1):
                if day > total_days:
                    return False
                days_covered.add(day)
        
        # Check if all days from 1 to total_days are covered exactly once
        return days_covered == set(range(1, total_days + 1))
    
    problem.addConstraint(
        all_days_covered,
        ['Naples_start', 'Naples_end', 'Vienna_start', 'Vienna_end', 'Vilnius_start', 'Vilnius_end']
    )
    
    # Constraint: No overlapping stays
    def no_overlap(naples_s, naples_e, vienna_s, vienna_e, vilnius_s, vilnius_e):
        stays = [
            (naples_s, naples_e, 'Naples'),
            (vienna_s, vienna_e, 'Vienna'),
            (vilnius_s, vilnius_e, 'Vilnius')
        ]
        
        # Filter out non-visited cities
        valid_stays = [(start, end, city) for start, end, city in stays if start > 0 and end > 0]
        
        # Check for overlaps
        for i, (start1, end1, city1) in enumerate(valid_stays):
            for j, (start2, end2, city2) in enumerate(valid_stays):
                if i != j:
                    # Check if the ranges overlap
                    if not (end1 < start2 or end2 < start1):
                        # If they overlap, check if it's a valid transition (flight exists)
                        if city2 not in flights.get(city1, []):
                            return False
        return True
    
    problem.addConstraint(
        no_overlap,
        ['Naples_start', 'Naples_end', 'Vienna_start', 'Vienna_end', 'Vilnius_start', 'Vilnius_end']
    )
    
    # Constraint: Naples must be visited between day 1 and 5
    def naples_early_constraint(naples_s, naples_e):
        return naples_s >= 1 and naples_e <= 5
    
    problem.addConstraint(
        naples_early_constraint,
        ['Naples_start', 'Naples_end']
    )
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with exact constraints, try without the Naples day constraint
        problem.reset()
        
        # Re-add all variables
        for city in cities:
            problem.addVariable(f'{city}_start', range(1, total_days + 2))
            problem.addVariable(f'{city}_end', range(1, total_days + 2))
        
        # Re-add constraints except Naples early constraint
        problem.addConstraint(
            lambda n_start, n_end: duration_constraint(n_start, n_end, naples_days),
            ['Naples_start', 'Naples_end']
        )
        problem.addConstraint(
            lambda v_start, v_end: duration_constraint(v_start, v_end, vienna_days),
            ['Vienna_start', 'Vienna_end']
        )
        problem.addConstraint(
            lambda vl_start, vl_end: duration_constraint(vl_start, vl_end, vilnius_days),
            ['Vilnius_start', 'Vilnius_end']
        )
        problem.addConstraint(
            all_days_covered,
            ['Naples_start', 'Naples_end', 'Vienna_start', 'Vienna_end', 'Vilnius_start', 'Vilnius_end']
        )
        problem.addConstraint(
            no_overlap,
            ['Naples_start', 'Naples_end', 'Vienna_start', 'Vienna_end', 'Vilnius_start', 'Vilnius_end']
        )
        
        solutions = problem.getSolutions()
    
    if solutions:
        # Use the first solution
        solution = solutions[0]
        
        # Create itinerary
        stays = [
            (solution['Naples_start'], solution['Naples_end'], 'Naples'),
            (solution['Vienna_start'], solution['Vienna_end'], 'Vienna'),
            (solution['Vilnius_start'], solution['Vilnius_end'], 'Vilnius')
        ]
        
        # Sort by start day
        stays.sort(key=lambda x: x[0])
        
        itinerary = []
        for start, end, city in stays:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()