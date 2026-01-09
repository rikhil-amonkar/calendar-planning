import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ['Lyon', 'Bucharest', 'Porto']
    required_days = {
        'Lyon': 7,
        'Bucharest': 7,
        'Porto': 4
    }
    
    total_days = 16
    
    # Define variables for start days of each city visit
    problem.addVariable('start_Lyon', range(1, total_days + 1))
    problem.addVariable('start_Bucharest', range(1, total_days + 1))
    problem.addVariable('start_Porto', range(1, total_days + 1))
    
    # Add constraint that all start days must be different
    problem.addConstraint(AllDifferentConstraint(), ['start_Lyon', 'start_Bucharest', 'start_Porto'])
    
    # Constraint: Total days must fit within 16 days without overlaps
    def no_overlap_constraint(lyon_start, bucharest_start, porto_start):
        # Calculate end days for each city
        lyon_end = lyon_start + required_days['Lyon'] - 1
        bucharest_end = bucharest_start + required_days['Bucharest'] - 1
        porto_end = porto_start + required_days['Porto'] - 1
        
        # All visits must be within the 16-day range
        if lyon_end > total_days or bucharest_end > total_days or porto_end > total_days:
            return False
        
        # Check for overlaps - visits cannot overlap
        intervals = [
            (lyon_start, lyon_end),
            (bucharest_start, bucharest_end),
            (porto_start, porto_end)
        ]
        
        # Check if any intervals overlap
        for i in range(len(intervals)):
            for j in range(i + 1, len(intervals)):
                start1, end1 = intervals[i]
                start2, end2 = intervals[j]
                # Check if intervals overlap
                if not (end1 < start2 or end2 < start1):
                    return False
        
        return True
    
    problem.addConstraint(no_overlap_constraint, 
                         ['start_Lyon', 'start_Bucharest', 'start_Porto'])
    
    # Constraint: Wedding in Bucharest between day 1 and 7
    def wedding_constraint(bucharest_start):
        bucharest_end = bucharest_start + required_days['Bucharest'] - 1
        # Bucharest visit must include at least one day between 1 and 7
        return bucharest_start <= 7 and bucharest_end >= 1
    
    problem.addConstraint(wedding_constraint, ['start_Bucharest'])
    
    # Constraint: Direct flights only (Bucharest-Lyon, Lyon-Porto)
    # This means Lyon must be visited immediately before or after both Bucharest and Porto
    def flight_constraint(lyon_start, bucharest_start, porto_start):
        visits = [
            (lyon_start, 'Lyon'),
            (bucharest_start, 'Bucharest'),
            (porto_start, 'Porto')
        ]
        
        # Sort by start day to get chronological order
        visits.sort()
        order = [visit[1] for visit in visits]
        
        # Check if Lyon is adjacent to both Bucharest and Porto in the itinerary
        lyon_index = order.index('Lyon')
        
        # Lyon must be adjacent to Bucharest
        bucharest_index = order.index('Bucharest')
        lyon_bucharest_adjacent = abs(lyon_index - bucharest_index) == 1
        
        # Lyon must be adjacent to Porto
        porto_index = order.index('Porto')
        lyon_porto_adjacent = abs(lyon_index - porto_index) == 1
        
        return lyon_bucharest_adjacent and lyon_porto_adjacent
    
    problem.addConstraint(flight_constraint, 
                         ['start_Lyon', 'start_Bucharest', 'start_Porto'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create the itinerary in chronological order
    visits = [
        (solution['start_Lyon'], solution['start_Lyon'] + required_days['Lyon'] - 1, 'Lyon'),
        (solution['start_Bucharest'], solution['start_Bucharest'] + required_days['Bucharest'] - 1, 'Bucharest'),
        (solution['start_Porto'], solution['start_Porto'] + required_days['Porto'] - 1, 'Porto')
    ]
    
    # Sort by start day
    visits.sort()
    
    # Format the itinerary
    itinerary = []
    for start, end, city in visits:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))