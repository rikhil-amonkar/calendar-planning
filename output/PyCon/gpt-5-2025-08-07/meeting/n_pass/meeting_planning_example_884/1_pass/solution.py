def main():
    # Define locations
    locations = [
        "Richmond District", "Chinatown", "Sunset District", "Alamo Square", 
        "Financial District", "North Beach", "Embarcadero", "Presidio", 
        "Golden Gate Park", "Bayview"
    ]
    
    # Travel time matrix (in minutes)
    travel_times = {
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Bayview"): 27,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Bayview"): 20,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Bayview"): 22,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Bayview"): 16,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Bayview"): 19,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Bayview"): 25,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Bayview"): 21,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Bayview"): 31,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Bayview"): 23,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "North Beach"): 22,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Golden Gate Park"): 22,
    }
    
    # Friend constraints
    friends = {
        "Robert": {
            "location": "Chinatown",
            "available_start": datetime.strptime("7:45", "%H:%M"),
            "available_end": datetime.strptime("17:30", "%H:%M"),
            "min_duration": 120
        },
        "David": {
            "location": "Sunset District",
            "available_start": datetime.strptime("12:30", "%H:%M"),
            "available_end": datetime.strptime("19:45", "%H:%M"),
            "min_duration": 45
        },
        "Matthew": {
            "location": "Alamo Square",
            "available_start": datetime.strptime("8:45", "%H:%M"),
            "available_end": datetime.strptime("13:45", "%H:%M"),
            "min_duration": 90
        },
        "Jessica": {
            "location": "Financial District",
            "available_start": datetime.strptime("9:30", "%H:%M"),
            "available_end": datetime.strptime("18:45", "%H:%M"),
            "min_duration": 45
        },
        "Melissa": {
            "location": "North Beach",
            "available_start": datetime.strptime("7:15", "%H:%M"),
            "available_end": datetime.strptime("16:45", "%H:%M"),
            "min_duration": 45
        },
        "Mark": {
            "location": "Embarcadero",
            "available_start": datetime.strptime("15:15", "%H:%M"),
            "available_end": datetime.strptime("17:00", "%H:%M"),
            "min_duration": 45
        },
        "Deborah": {
            "location": "Presidio",
            "available_start": datetime.strptime("19:00", "%H:%M"),
            "available_end": datetime.strptime("19:45", "%H:%M"),
            "min_duration": 45
        },
        "Karen": {
            "location": "Golden Gate Park",
            "available_start": datetime.strptime("19:30", "%H:%M"),
            "available_end": datetime.strptime("22:00", "%H:%M"),
            "min_duration": 120
        },
        "Laura": {
            "location": "Bayview",
            "available_start": datetime.strptime("21:15", "%H:%M"),
            "available_end": datetime.strptime("22:15", "%H:%M"),
            "min_duration": 15
        }
    }
    
    # Start time
    start_time = datetime.strptime("9:00", "%H:%M")
    current_location = "Richmond District"
    
    # Create problem
    problem = constraint.Problem()
    
    # Define variables for each friend: start_time (in minutes from 9:00)
    friend_names = list(friends.keys())
    
    # Add variables for start times (in minutes from 9:00)
    for friend in friend_names:
        min_start = 0  # 9:00 AM
        max_end = 780  # 22:00 (10:00 PM) - 9:00 AM = 13 hours = 780 minutes
        problem.addVariable(f"{friend}_start", range(min_start, max_end + 1))
        problem.addVariable(f"{friend}_duration", [friends[friend]["min_duration"]])
    
    # Add ordering constraints based on logical sequence
    # Matthew is only available until 1:45 PM, so he should be early
    matthew_end_min = (friends["Matthew"]["available_end"] - start_time).total_seconds() // 60
    problem.addConstraint(lambda m_start, m_dur: m_start + m_dur <= matthew_end_min, 
                         ["Matthew_start", "Matthew_duration"])
    
    # David is only available from 12:30 PM
    david_start_min = (friends["David"]["available_start"] - start_time).total_seconds() // 60
    problem.addConstraint(lambda d_start: d_start >= david_start_min, ["David_start"])
    
    # Mark is only available from 3:15 PM
    mark_start_min = (friends["Mark"]["available_start"] - start_time).total_seconds() // 60
    problem.addConstraint(lambda m_start: m_start >= mark_start_min, ["Mark_start"])
    
    # Deborah is only available from 7:00 PM
    deborah_start_min = (friends["Deborah"]["available_start"] - start_time).total_seconds() // 60
    problem.addConstraint(lambda d_start: d_start >= deborah_start_min, ["Deborah_start"])
    
    # Karen is only available from 7:30 PM
    karen_start_min = (friends["Karen"]["available_start"] - start_time).total_seconds() // 60
    problem.addConstraint(lambda k_start: k_start >= karen_start_min, ["Karen_start"])
    
    # Laura is only available from 9:15 PM
    laura_start_min = (friends["Laura"]["available_start"] - start_time).total_seconds() // 60
    problem.addConstraint(lambda l_start: l_start >= laura_start_min, ["Laura_start"])
    
    # Define a simple ordering that makes sense geographically and temporally
    def simple_ordering_constraint(*starts):
        matthew, robert, jessica, melissa, david, mark, deborah, karen, laura = starts
        
        # Matthew should be early (before 1:45 PM)
        if matthew > 285:  # 1:45 PM = 285 minutes from 9:00 AM
            return False
            
        # Robert needs 2 hours, so schedule him reasonably
        if robert > 360:  # 3:00 PM
            return False
            
        # David should be after lunch (12:30 PM)
        if david < 210:  # 12:30 PM = 210 minutes from 9:00 AM
            return False
            
        # Mark should be in the afternoon
        if mark < 375:  # 3:15 PM = 375 minutes from 9:00 AM
            return False
            
        # Evening meetings in order: Deborah, Karen, Laura
        if deborah >= karen or karen >= laura:
            return False
            
        return True
    
    # Apply the simple ordering constraint
    problem.addConstraint(simple_ordering_constraint, 
                         [f"{f}_start" for f in friend_names])
    
    # Try to find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: create a reasonable schedule manually
        itinerary = []
        current_time = start_time
        
        # Start with Matthew (Alamo Square) - earliest availability
        matthew_duration = friends["Matthew"]["min_duration"]
        matthew_start = max(current_time, friends["Matthew"]["available_start"])
        matthew_end = matthew_start + timedelta(minutes=matthew_duration)
        itinerary.append({
            "action": "meet",
            "location": "Alamo Square",
            "person": "Matthew",
            "start_time": matthew_start.strftime("%H:%M"),
            "end_time": matthew_end.strftime("%H:%M")
        })
        
        # Travel to Chinatown for Robert
        travel_time = travel_times[("Alamo Square", "Chinatown")]
        current_time = matthew_end + timedelta(minutes=travel_time)
        
        # Meet Robert
        robert_duration = friends["Robert"]["min_duration"]
        robert_start = max(current_time, friends["Robert"]["available_start"])
        robert_end = robert_start + timedelta(minutes=robert_duration)
        itinerary.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Robert",
            "start_time": robert_start.strftime("%H:%M"),
            "end_time": robert_end.strftime("%H:%M")
        })
        
        # Travel to Financial District for Jessica
        travel_time = travel_times[("Chinatown", "Financial District")]
        current_time = robert_end + timedelta(minutes=travel_time)
        
        # Meet Jessica
        jessica_duration = friends["Jessica"]["min_duration"]
        jessica_start = max(current_time, friends["Jessica"]["available_start"])
        jessica_end = jessica_start + timedelta(minutes=jessica_duration)
        itinerary.append({
            "action": "meet",
            "location": "Financial District",
            "person": "Jessica",
            "start_time": jessica_start.strftime("%H:%M"),
            "end_time": jessica_end.strftime("%H:%M")
        })
        
        # Travel to North Beach for Melissa
        travel_time = travel_times[("Financial District", "North Beach")]
        current_time = jessica_end + timedelta(minutes=travel_time)
        
        # Meet Melissa
        melissa_duration = friends["Melissa"]["min_duration"]
        melissa_start = max(current_time, friends["Melissa"]["available_start"])
        melissa_end = melissa_start + timedelta(minutes=melissa_duration)
        itinerary.append({
            "action": "meet",
            "location": "North Beach",
            "person": "Melissa",
            "start_time": melissa_start.strftime("%H:%M"),
            "end_time": melissa_end.strftime("%H:%M")
        })
        
        # Travel to Sunset District for David
        travel_time = travel_times[("North Beach", "Sunset District")]
        current_time = melissa_end + timedelta(minutes=travel_time)
        
        # Meet David
        david_duration = friends["David"]["min_duration"]
        david_start = max(current_time, friends["David"]["available_start"])
        david_end = david_start + timedelta(minutes=david_duration)
        itinerary.append({
            "action": "meet",
            "location": "Sunset District",
            "person": "David",
            "start_time": david_start.strftime("%H:%M"),
            "end_time": david_end.strftime("%H:%M")
        })
        
        # Travel to Embarcadero for Mark
        travel_time = travel_times[("Sunset District", "Embarcadero")]
        current_time = david_end + timedelta(minutes=travel_time)
        
        # Meet Mark
        mark_duration = friends["Mark"]["min_duration"]
        mark_start = max(current_time, friends["Mark"]["available_start"])
        mark_end = mark_start + timedelta(minutes=mark_duration)
        itinerary.append({
            "action": "meet",
            "location": "Embarcadero",
            "person": "Mark",
            "start_time": mark_start.strftime("%H:%M"),
            "end_time": mark_end.strftime("%H:%M")
        })
        
        # Travel to Presidio for Deborah
        travel_time = travel_times[("Embarcadero", "Presidio")]
        current_time = mark_end + timedelta(minutes=travel_time)
        
        # Meet Deborah
        deborah_duration = friends["Deborah"]["min_duration"]
        deborah_start = max(current_time, friends["Deborah"]["available_start"])
        deborah_end = deborah_start + timedelta(minutes=deborah_duration)
        itinerary.append({
            "action": "meet",
            "location": "Presidio",
            "person": "Deborah",
            "start_time": deborah_start.strftime("%H:%M"),
            "end_time": deborah_end.strftime("%H:%M")
        })
        
        # Travel to Golden Gate Park for Karen
        travel_time = travel_times[("Presidio", "Golden Gate Park")]
        current_time = deborah_end + timedelta(minutes=travel_time)
        
        # Meet Karen
        karen_duration = friends["Karen"]["min_duration"]
        karen_start = max(current_time, friends["Karen"]["available_start"])
        karen_end = karen_start + timedelta(minutes=karen_duration)
        itinerary.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Karen",
            "start_time": karen_start.strftime("%H