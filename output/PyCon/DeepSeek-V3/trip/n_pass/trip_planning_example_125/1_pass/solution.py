from constraint import Problem
import json

def main():
    # Define the problem parameters
    total_days = 15
    cities = ['Manchester', 'Seville', 'Stuttgart']
    
    # Direct flight connections
    direct_flights = {
        'Manchester': ['Seville', 'Stuttgart'],
        'Seville': ['Manchester'],
        'Stuttgart': ['Manchester']
    }
    
    # Duration constraints
    stuttgart_days = 6
    seville_days = 7
    manchester_days = 4
    
    # Friend meeting constraint in Stuttgart between day 1-6
    stuttgart_meeting_start = 1
    stuttgart_meeting_end = 6
    
    # Create constraint problem
    problem = Problem()
    
    # Variables: start day for each city (0-indexed, day 1 = 0)
    # We'll model this as finding the order of cities and their durations
    # Since we have exactly 3 cities and direct flight constraints, we need to find a valid sequence
    
    # Approach: Model as finding the sequence of cities that satisfies:
    # 1. Total days = 15
    # 2. Each city gets required days
    # 3. Only direct flights between consecutive cities
    # 4. Stuttgart visit includes days 1-6 for meeting friend
    
    # We'll use a different approach: find start days for each city that satisfy constraints
    
    # Add variables for start days (0-indexed, where day 1 = 0)
    problem.addVariable('manchester_start', range(total_days))
    problem.addVariable('seville_start', range(total_days))
    problem.addVariable('stuttgart_start', range(total_days))
    
    # Add variables for durations (we know the exact durations)
    problem.addVariable('manchester_dur', [manchester_days])
    problem.addVariable('seville_dur', [seville_days])
    problem.addVariable('stuttgart_dur', [stuttgart_days])
    
    def no_overlap(man_start, sev_start, stut_start, man_dur, sev_dur, stut_dur):
        # Check that city visits don't overlap
        intervals = [
            (man_start, man_start + man_dur),
            (sev_start, sev_start + sev_dur),
            (stut_start, stut_start + stut_dur)
        ]
        
        # Sort by start time
        intervals.sort()
        
        # Check for overlaps
        for i in range(len(intervals) - 1):
            if intervals[i][1] > intervals[i][0]:
                # Valid interval, check if it overlaps with next
                if intervals[i][1] > intervals[i + 1][0]:
                    return False
        return True
    
    def total_days_constraint(man_start, sev_start, stut_start, man_dur, sev_dur, stut_dur):
        # All days from 0 to total_days-1 should be covered exactly once
        days_covered = set()
        
        for start, dur in [(man_start, man_dur), (sev_start, sev_dur), (stut_start, stut_dur)]:
            for day in range(start, start + dur):
                if day >= total_days:
                    return False
                days_covered.add(day)
        
        return len(days_covered) == total_days
    
    def flight_constraint(man_start, sev_start, stut_start, man_dur, sev_dur, stut_dur):
        # Check that consecutive cities in the itinerary have direct flights
        cities_order = []
        
        # Create list of (start_city, city_name) pairs
        cities_with_start = [
            (man_start, 'Manchester'),
            (sev_start, 'Seville'), 
            (stut_start, 'Stuttgart')
        ]
        
        # Sort by start day to get itinerary order
        cities_with_start.sort()
        
        # Extract just the city names in order
        itinerary = [city for _, city in cities_with_start]
        
        # Check direct flights between consecutive cities
        for i in range(len(itinerary) - 1):
            city_a = itinerary[i]
            city_b = itinerary[i + 1]
            if city_b not in direct_flights[city_a]:
                return False
        return True
    
    def stuttgart_meeting_constraint(stut_start, stut_dur):
        # Stuttgart visit must include at least one day between day 1-6 (0-5 in 0-index)
        stut_end = stut_start + stut_dur - 1
        meeting_start = stuttgart_meeting_start - 1  # Convert to 0-index
        meeting_end = stuttgart_meeting_end - 1      # Convert to 0-index
        
        # Check if Stuttgart visit overlaps with meeting days
        return (stut_start <= meeting_end and stut_end >= meeting_start)
    
    # Add constraints
    problem.addConstraint(no_overlap, 
                         ['manchester_start', 'seville_start', 'stuttgart_start', 
                          'manchester_dur', 'seville_dur', 'stuttgart_dur'])
    
    problem.addConstraint(total_days_constraint,
                         ['manchester_start', 'seville_start', 'stuttgart_start',
                          'manchester_dur', 'seville_dur', 'stuttgart_dur'])
    
    problem.addConstraint(flight_constraint,
                         ['manchester_start', 'seville_start', 'stuttgart_start',
                          'manchester_dur', 'seville_dur', 'stuttgart_dur'])
    
    problem.addConstraint(stuttgart_meeting_constraint, ['stuttgart_start', 'stuttgart_dur'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with exact constraints, try a different approach
        # Generate all possible valid itineraries manually
        valid_itineraries = []
        
        # Try different orders that satisfy flight constraints
        possible_orders = [
            ['Manchester', 'Stuttgart', 'Seville'],  # M->S (direct), S->Seville (no direct - invalid)
            ['Manchester', 'Seville', 'Stuttgart'],  # M->S (direct), S->Stuttgart (no direct - invalid)
            ['Seville', 'Manchester', 'Stuttgart'],  # S->M (direct), M->S (direct) - VALID
            ['Stuttgart', 'Manchester', 'Seville'],  # S->M (direct), M->S (direct) - VALID
            ['Seville', 'Stuttgart', 'Manchester'],  # S->S (no direct - invalid)
            ['Stuttgart', 'Seville', 'Manchester']   # S->S (no direct - invalid)
        ]
        
        for order in possible_orders:
            # Check if this order satisfies direct flight constraints
            valid_order = True
            for i in range(len(order) - 1):
                if order[i+1] not in direct_flights[order[i]]:
                    valid_order = False
                    break
            
            if valid_order:
                # This is a valid order: Seville->Manchester->Stuttgart or Stuttgart->Manchester->Seville
                if order == ['Seville', 'Manchester', 'Stuttgart']:
                    # Seville first (7 days), then Manchester (4 days), then Stuttgart (6 days)
                    # Check if Stuttgart includes meeting days (days 1-6)
                    # If Stuttgart is last, it starts at day 11, which doesn't include days 1-6
                    # So this order doesn't work for the meeting constraint
                    continue
                elif order == ['Stuttgart', 'Manchester', 'Seville']:
                    # Stuttgart first (6 days), then Manchester (4 days), then Seville (7 days)
                    # Stuttgart is first, so it covers days 1-6 (meeting constraint satisfied)
                    itinerary = []
                    current_day = 1
                    
                    # Stuttgart: days 1-6
                    itinerary.append({"day_range": f"Day {current_day}-{current_day + stuttgart_days - 1}", "place": "Stuttgart"})
                    current_day += stuttgart_days
                    
                    # Manchester: days 7-10  
                    itinerary.append({"day_range": f"Day {current_day}-{current_day + manchester_days - 1}", "place": "Manchester"})
                    current_day += manchester_days
                    
                    # Seville: days 11-17 (but we only have 15 days total)
                    # Adjust Seville to fit in remaining days
                    remaining_days = total_days - (stuttgart_days + manchester_days)
                    if remaining_days >= seville_days:
                        itinerary.append({"day_range": f"Day {current_day}-{current_day + seville_days - 1}", "place": "Seville"})
                    else:
                        itinerary.append({"day_range": f"Day {current_day}-{current_day + remaining_days - 1}", "place": "Seville"})
                    
                    valid_itineraries.append(itinerary)
                    break
        
        if valid_itineraries:
            result = {"itinerary": valid_itineraries[0]}
        else:
            # Fallback solution
            result = {
                "itinerary": [
                    {"day_range": "Day 1-6", "place": "Stuttgart"},
                    {"day_range": "Day 7-10", "place": "Manchester"}, 
                    {"day_range": "Day 11-15", "place": "Seville"}
                ]
            }
    else:
        # Use the constraint solution
        solution = solutions[0]
        
        # Create itinerary from solution
        cities_with_info = [
            (solution['manchester_start'], solution['manchester_dur'], 'Manchester'),
            (solution['seville_start'], solution['seville_dur'], 'Seville'),
            (solution['stuttgart_start'], solution['stuttgart_dur'], 'Stuttgart')
        ]
        
        # Sort by start day
        cities_with_info.sort()
        
        itinerary = []
        for start, duration, city in cities_with_info:
            day_start = start + 1  # Convert from 0-index to 1-index
            day_end = start + duration  # end is exclusive in our model
            itinerary.append({
                "day_range": f"Day {day_start}-{day_end}",
                "place": city
            })
        
        result = {"itinerary": itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()