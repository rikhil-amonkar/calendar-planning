import json
from constraint import Problem

def main():
    # Define the problem parameters
    total_days = 12
    cities = ["Milan", "Seville", "Naples"]
    
    # Direct flight constraints (one-way is sufficient)
    direct_flights = {
        "Milan": ["Seville", "Naples"],
        "Seville": ["Milan"],
        "Naples": ["Milan"]
    }
    
    # Create constraint problem
    problem = Problem()
    
    # Add variables for start day of each city stay
    # Days start from 1
    problem.addVariable("milan_start", range(1, total_days + 1))
    problem.addVariable("seville_start", range(1, total_days + 1))
    problem.addVariable("naples_start", range(1, total_days + 1))
    
    # Fixed durations for each stay
    milan_duration = 7
    seville_duration = 4  
    naples_duration = 3
    
    # Constraint: All stays must end within the 12-day period
    def stays_within_period(m_start, s_start, n_start):
        m_end = m_start + milan_duration - 1
        s_end = s_start + seville_duration - 1
        n_end = n_start + naples_duration - 1
        return (m_end <= total_days and s_end <= total_days and n_end <= total_days)
    
    problem.addConstraint(stays_within_period, ["milan_start", "seville_start", "naples_start"])
    
    # Constraint: No overlapping stays
    def no_overlap(m_start, s_start, n_start):
        m_end = m_start + milan_duration - 1
        s_end = s_start + seville_duration - 1
        n_end = n_start + naples_duration - 1
        
        # Check all pairs for overlap
        # We allow consecutive stays (end day of one = start day of next - 1)
        milan_seville = (m_end < s_start) or (s_end < m_start)
        milan_naples = (m_end < n_start) or (n_end < m_start)
        seville_naples = (s_end < n_start) or (n_end < s_start)
        
        return milan_seville and milan_naples and seville_naples
    
    problem.addConstraint(no_overlap, ["milan_start", "seville_start", "naples_start"])
    
    # Constraint: Seville must include days 9-12
    # With 4-day duration, Seville must start on day 9 to include both day 9 and day 12
    def seville_show_constraint(s_start):
        s_end = s_start + seville_duration - 1
        return s_start <= 9 and s_end >= 12
    
    problem.addConstraint(seville_show_constraint, ["seville_start"])
    
    # Constraint: Valid flight connections between consecutive stays
    def valid_flights(m_start, s_start, n_start):
        # Create list of stays with city and start day
        stays = [
            ("Milan", m_start, milan_duration),
            ("Seville", s_start, seville_duration), 
            ("Naples", n_start, naples_duration)
        ]
        
        # Sort stays by start day to get chronological order
        stays.sort(key=lambda x: x[1])
        
        # Check flight connections between consecutive stays
        for i in range(len(stays) - 1):
            current_city = stays[i][0]
            next_city = stays[i + 1][0]
            
            # Check if direct flight exists from current to next city
            if next_city not in direct_flights.get(current_city, []):
                return False
        
        return True
    
    problem.addConstraint(valid_flights, ["milan_start", "seville_start", "naples_start"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found, try relaxing the Seville constraint
        # Remove the Seville constraint and find all possible solutions
        problem.reset()
        
        # Re-add all constraints except Seville show constraint
        problem.addVariable("milan_start", range(1, total_days + 1))
        problem.addVariable("seville_start", range(1, total_days + 1))
        problem.addVariable("naples_start", range(1, total_days + 1))
        
        problem.addConstraint(stays_within_period, ["milan_start", "seville_start", "naples_start"])
        problem.addConstraint(no_overlap, ["milan_start", "seville_start", "naples_start"])
        problem.addConstraint(valid_flights, ["milan_start", "seville_start", "naples_start"])
        
        # Find solutions where Seville includes days 9-12
        solutions = []
        all_solutions = problem.getSolutions()
        for sol in all_solutions:
            s_start = sol["seville_start"]
            s_end = s_start + seville_duration - 1
            if s_start <= 9 and s_end >= 12:
                solutions.append(sol)
        
        if not solutions:
            result = {"error": "No valid itinerary found"}
            print(json.dumps(result))
            return
    
    # Take the first solution
    solution = solutions[0]
    
    # Create the itinerary in chronological order
    stays = [
        {"city": "Milan", "start": solution["milan_start"], "duration": milan_duration},
        {"city": "Seville", "start": solution["seville_start"], "duration": seville_duration},
        {"city": "Naples", "start": solution["naples_start"], "duration": naples_duration}
    ]
    
    # Sort by start day
    stays.sort(key=lambda x: x["start"])
    
    # Build the itinerary with day ranges
    itinerary = []
    for stay in stays:
        start_day = stay["start"]
        end_day = start_day + stay["duration"] - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": stay["city"]})
    
    # Output the result
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()