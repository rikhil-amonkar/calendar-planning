import constraint
import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes
    travel_times = {
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Fisherman\'s Wharf'): 29,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Fisherman\'s Wharf', 'Sunset District'): 27,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Presidio'): 17
    }
    
    # Convert all times to minutes since midnight
    start_time = time_to_minutes("9:00")  # Arrive at Sunset District
    
    # Friend availability windows
    william_start = time_to_minutes("18:30")
    william_end = time_to_minutes("20:45")
    william_min = 105
    
    michelle_start = time_to_minutes("8:15")
    michelle_end = time_to_minutes("14:00")
    michelle_min = 15
    
    george_start = time_to_minutes("10:30")
    george_end = time_to_minutes("18:45")
    george_min = 30
    
    robert_start = time_to_minutes("9:00")
    robert_end = time_to_minutes("13:45")
    robert_min = 30
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start times for each meeting
    # We'll use minutes since midnight
    problem.addVariable("michelle_start", range(michelle_start, michelle_end - michelle_min + 1))
    problem.addVariable("george_start", range(george_start, george_end - george_min + 1))
    problem.addVariable("robert_start", range(robert_start, robert_end - robert_min + 1))
    problem.addVariable("william_start", range(william_start, william_end - william_min + 1))
    
    # Order constraints - we need to decide the sequence of meetings
    # Let's add variables for the order
    problem.addVariable("order_michelle", [1, 2, 3, 4])
    problem.addVariable("order_george", [1, 2, 3, 4])
    problem.addVariable("order_robert", [1, 2, 3, 4])
    problem.addVariable("order_william", [1, 2, 3, 4])
    
    # All orders must be different
    problem.addConstraint(constraint.AllDifferentConstraint(), 
                         ["order_michelle", "order_george", "order_robert", "order_william"])
    
    def travel_constraint(m_start, g_start, r_start, w_start, 
                         m_order, g_order, r_order, w_order):
        # Create list of meetings with their order and times
        meetings = [
            ("Michelle", "Chinatown", m_start, m_start + michelle_min, m_order),
            ("George", "Presidio", g_start, g_start + george_min, g_order),
            ("Robert", "Fisherman's Wharf", r_start, r_start + robert_min, r_order),
            ("William", "Russian Hill", w_start, w_start + william_min, w_order)
        ]
        
        # Sort by order
        meetings.sort(key=lambda x: x[4])
        
        current_time = start_time
        current_location = "Sunset District"
        
        for i, (person, location, start, end, order) in enumerate(meetings):
            # Check if we can travel to this location in time
            travel_time = travel_times.get((current_location, location), 60)
            
            # Arrival time at next meeting
            arrival_time = current_time + travel_time
            
            # We must arrive before or at the meeting start time
            if arrival_time > start:
                return False
            
            # Update current time and location
            current_time = end
            current_location = location
            
            # Check if this meeting fits within the person's availability
            if start < time_to_minutes("8:15") and person == "Michelle":
                return False
            if end > time_to_minutes("14:00") and person == "Michelle":
                return False
            if start < time_to_minutes("10:30") and person == "George":
                return False
            if end > time_to_minutes("18:45") and person == "George":
                return False
            if start < time_to_minutes("9:00") and person == "Robert":
                return False
            if end > time_to_minutes("13:45") and person == "Robert":
                return False
            if start < time_to_minutes("18:30") and person == "William":
                return False
            if end > time_to_minutes("20:45") and person == "William":
                return False
        
        return True
    
    problem.addConstraint(travel_constraint, 
                         ["michelle_start", "george_start", "robert_start", "william_start",
                          "order_michelle", "order_george", "order_robert", "order_william"])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many as possible with a simpler approach
        itinerary = []
        
        # Try Robert first (earliest availability)
        travel_to_robert = travel_times[('Sunset District', 'Fisherman\'s Wharf')]
        robert_meet_start = max(start_time + travel_to_robert, robert_start)
        robert_meet_end = min(robert_meet_start + robert_min, robert_end)
        
        if robert_meet_end <= robert_end and robert_meet_start >= robert_start:
            itinerary.append({
                "action": "meet",
                "location": "Fisherman's Wharf",
                "person": "Robert",
                "start_time": minutes_to_time(robert_meet_start),
                "end_time": minutes_to_time(robert_meet_end)
            })
            current_time = robert_meet_end
            current_location = "Fisherman's Wharf"
        else:
            current_time = start_time
            current_location = "Sunset District"
        
        # Try Michelle next
        travel_to_michelle = travel_times.get((current_location, 'Chinatown'), 60)
        michelle_meet_start = max(current_time + travel_to_michelle, michelle_start)
        michelle_meet_end = min(michelle_meet_start + michelle_min, michelle_end)
        
        if michelle_meet_end <= michelle_end and michelle_meet_start >= michelle_start:
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Michelle",
                "start_time": minutes_to_time(michelle_meet_start),
                "end_time": minutes_to_time(michelle_meet_end)
            })
            current_time = michelle_meet_end
            current_location = "Chinatown"
        
        # Try George next
        travel_to_george = travel_times.get((current_location, 'Presidio'), 60)
        george_meet_start = max(current_time + travel_to_george, george_start)
        george_meet_end = min(george_meet_start + george_min, george_end)
        
        if george_meet_end <= george_end and george_meet_start >= george_start:
            itinerary.append({
                "action": "meet",
                "location": "Presidio",
                "person": "George",
                "start_time": minutes_to_time(george_meet_start),
                "end_time": minutes_to_time(george_meet_end)
            })
            current_time = george_meet_end
            current_location = "Presidio"
        
        # Try William last
        travel_to_william = travel_times.get((current_location, 'Russian Hill'), 60)
        william_meet_start = max(current_time + travel_to_william, william_start)
        william_meet_end = min(william_meet_start + william_min, william_end)
        
        if william_meet_end <= william_end and william_meet_start >= william_start:
            itinerary.append({
                "action": "meet",
                "location": "Russian Hill",
                "person": "William",
                "start_time": minutes_to_time(william_meet_start),
                "end_time": minutes_to_time(william_meet_end)
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
        return
    
    # Use the first valid solution
    sol = solutions[0]
    
    # Create itinerary in correct order
    meetings = [
        ("Michelle", "Chinatown", sol["michelle_start"], sol["michelle_start"] + michelle_min, sol["order_michelle"]),
        ("George", "Presidio", sol["george_start"], sol["george_start"] + george_min, sol["order_george"]),
        ("Robert", "Fisherman's Wharf", sol["robert_start"], sol["robert_start"] + robert_min, sol["order_robert"]),
        ("William", "Russian Hill", sol["william_start"], sol["william_start"] + william_min, sol["order_william"])
    ]
    
    # Sort by order
    meetings.sort(key=lambda x: x[4])
    
    itinerary = []
    for person, location, start, end, order in meetings:
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()