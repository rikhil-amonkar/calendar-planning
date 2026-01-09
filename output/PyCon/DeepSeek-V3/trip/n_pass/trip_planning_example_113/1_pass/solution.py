import json
from constraint import Problem

def main():
    # Define the problem parameters
    total_days = 12
    cities = ["Milan", "Seville", "Naples"]
    
    # Direct flight constraints
    direct_flights = {
        "Milan": ["Seville"],
        "Seville": ["Milan"],
        "Naples": ["Milan"],
        "Milan": ["Naples"]
    }
    
    # Create constraint problem
    problem = Problem()
    
    # Add variables for start day of each city stay
    # We'll model this as a sequence of stays with start days
    problem.addVariable("milan_start", range(1, total_days + 1))
    problem.addVariable("seville_start", range(1, total_days + 1))
    problem.addVariable("naples_start", range(1, total_days + 1))
    
    # Add variables for duration of each stay
    problem.addVariable("milan_duration", [7])  # Fixed 7 days in Milan
    problem.addVariable("seville_duration", [4])  # Fixed 4 days in Seville
    problem.addVariable("naples_duration", [3])  # Fixed 3 days in Naples
    
    # Constraint: All stays must be within the 12-day period
    def stays_within_period(m_start, s_start, n_start, m_dur, s_dur, n_dur):
        m_end = m_start + m_dur - 1
        s_end = s_start + s_dur - 1
        n_end = n_start + n_dur - 1
        return (m_end <= total_days and s_end <= total_days and n_end <= total_days)
    
    problem.addConstraint(stays_within_period, 
                         ["milan_start", "seville_start", "naples_start", 
                          "milan_duration", "seville_duration", "naples_duration"])
    
    # Constraint: No overlapping stays
    def no_overlap(m_start, s_start, n_start, m_dur, s_dur, n_dur):
        m_end = m_start + m_dur
        s_end = s_start + s_dur
        n_end = n_start + n_dur
        
        # Check all pairs for overlap
        overlaps = []
        overlaps.append(m_start < s_end and s_start < m_end)
        overlaps.append(m_start < n_end and n_start < m_end)
        overlaps.append(s_start < n_end and n_start < s_end)
        
        # Only one overlap should be True at most (for travel days)
        return sum(overlaps) <= 1
    
    problem.addConstraint(no_overlap, 
                         ["milan_start", "seville_start", "naples_start", 
                          "milan_duration", "seville_duration", "naples_duration"])
    
    # Constraint: Seville must include days 9-12
    def seville_show_constraint(s_start, s_dur):
        s_end = s_start + s_dur - 1
        return s_start <= 9 and s_end >= 12
    
    problem.addConstraint(seville_show_constraint, ["seville_start", "seville_duration"])
    
    # Constraint: Valid flight connections between consecutive stays
    def valid_flights(m_start, s_start, n_start, m_dur, s_dur, n_dur):
        stays = [
            ("Milan", m_start, m_dur),
            ("Seville", s_start, s_dur),
            ("Naples", n_start, n_dur)
        ]
        
        # Sort stays by start day
        stays.sort(key=lambda x: x[1])
        
        # Check flight connections between consecutive stays
        for i in range(len(stays) - 1):
            current_city = stays[i][0]
            next_city = stays[i + 1][0]
            
            # Check if direct flight exists
            if next_city not in direct_flights.get(current_city, []):
                return False
        
        return True
    
    problem.addConstraint(valid_flights, 
                         ["milan_start", "seville_start", "naples_start", 
                          "milan_duration", "seville_duration", "naples_duration"])
    
    # Constraint: All days must be covered exactly once (except travel days which are counted in both cities)
    def all_days_covered(m_start, s_start, n_start, m_dur, s_dur, n_dur):
        # Create a set of all covered days
        covered_days = set()
        
        # Add days for each stay
        for start, dur in [(m_start, m_dur), (s_start, s_dur), (n_start, n_dur)]:
            for day in range(start, start + dur):
                covered_days.add(day)
        
        # Check if all days from 1 to 12 are covered
        return covered_days == set(range(1, total_days + 1))
    
    problem.addConstraint(all_days_covered, 
                         ["milan_start", "seville_start", "naples_start", 
                          "milan_duration", "seville_duration", "naples_duration"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        result = {"error": "No valid itinerary found"}
        print(json.dumps(result))
        return
    
    # Take the first solution
    solution = solutions[0]
    
    # Create the itinerary in chronological order
    stays = [
        {"city": "Milan", "start": solution["milan_start"], "duration": solution["milan_duration"]},
        {"city": "Seville", "start": solution["seville_start"], "duration": solution["seville_duration"]},
        {"city": "Naples", "start": solution["naples_start"], "duration": solution["naples_duration"]}
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