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
    problem.addVariable("milan_start", range(1, total_days + 1))
    problem.addVariable("seville_start", range(1, total_days + 1))
    problem.addVariable("naples_start", range(1, total_days + 1))
    
    # Add variables for duration of each stay (fixed)
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
    
    # Constraint: No overlapping stays (except travel days)
    def no_overlap(m_start, s_start, n_start, m_dur, s_dur, n_dur):
        m_end = m_start + m_dur
        s_end = s_start + s_dur
        n_end = n_start + n_dur
        
        # Check all pairs for overlap - allow exactly 1 day gap for travel
        overlaps = []
        overlaps.append(m_start < s_end and s_start < m_end)  # Milan-Seville overlap
        overlaps.append(m_start < n_end and n_start < m_end)  # Milan-Naples overlap
        overlaps.append(s_start < n_end and n_start < s_end)  # Seville-Naples overlap
        
        # No overlaps allowed (stays should be sequential with travel days)
        return sum(overlaps) == 0
    
    problem.addConstraint(no_overlap, 
                         ["milan_start", "seville_start", "naples_start", 
                          "milan_duration", "seville_duration", "naples_duration"])
    
    # Constraint: Seville must include days 9-12
    def seville_show_constraint(s_start, s_dur):
        s_end = s_start + s_dur - 1
        # Seville must start on or before day 9 and end on or after day 12
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
            
            # Check if direct flight exists from current to next city
            if next_city not in direct_flights.get(current_city, []):
                return False
        
        return True
    
    problem.addConstraint(valid_flights, 
                         ["milan_start", "seville_start", "naples_start", 
                          "milan_duration", "seville_duration", "naples_duration"])
    
    # Constraint: All stays must fit within the 12 days with travel days
    def all_stays_fit(m_start, s_start, n_start, m_dur, s_dur, n_dur):
        stays = [
            ("Milan", m_start, m_dur),
            ("Seville", s_start, s_dur),
            ("Naples", n_start, n_dur)
        ]
        
        # Sort by start day
        stays.sort(key=lambda x: x[1])
        
        # Check if the total duration fits (including travel days)
        total_required_days = sum(dur for _, _, dur in stays) + (len(stays) - 1)  # + travel days
        
        # Also check that stays are sequential with gaps for travel
        for i in range(len(stays) - 1):
            current_end = stays[i][1] + stays[i][2] - 1
            next_start = stays[i + 1][1]
            
            # There should be at least 1 day gap for travel between stays
            if next_start <= current_end:
                return False
        
        return total_required_days <= total_days
    
    problem.addConstraint(all_stays_fit, 
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