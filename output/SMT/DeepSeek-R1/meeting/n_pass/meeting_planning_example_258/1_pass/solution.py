from z3 import *

# Define travel times between locations
travel_dict = {
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18
}

# Friend locations
loc_Betty = "Presidio"
loc_David = "Richmond District"
loc_Barbara = "Fisherman\'s Wharf"

# Start time at Embarcadero (9:00 AM in minutes from midnight)
start_Embarcadero = 9 * 60  # 540 minutes

# Availability and duration constraints
# Betty: 10:15 AM to 9:30 PM -> 615 to 1290 minutes
betty_available_start = 10 * 60 + 15  # 615
betty_available_end = 21 * 60 + 30    # 1290 (9:30 PM)
betty_duration = 45

# David: 1:00 PM to 8:15 PM -> 780 to 1215 minutes
david_available_start = 13 * 60       # 780
david_available_end = 20 * 60 + 15    # 1215
david_duration = 90

# Barbara: 9:15 AM to 8:15 PM -> 555 to 1215 minutes
barbara_available_start = 9 * 60 + 15  # 555
barbara_available_end = 20 * 60 + 15   # 1215
barbara_duration = 120

# Initialize Z3 solver with optimization
opt = Optimize()

# Boolean variables for meeting each friend
meet_Betty = Bool('meet_Betty')
meet_David = Bool('meet_David')
meet_Barbara = Bool('meet_Barbara')

# Start and end times for each meeting
start_Betty = Int('start_Betty')
end_Betty = Int('end_Betty')
start_David = Int('start_David')
end_David = Int('end_David')
start_Barbara = Int('start_Barbara')
end_Barbara = Int('end_Barbara')

# Order variables between meetings
Betty_before_David = Bool('Betty_before_David')
Betty_before_Barbara = Bool('Betty_before_Barbara')
David_before_Barbara = Bool('David_before_Barbara')

# Constraints for meeting times and durations if meeting occurs
opt.add(If(meet_Betty, 
          And(start_Betty >= betty_available_start, 
              end_Betty == start_Betty + betty_duration,
              end_Betty <= betty_available_end),
          True))
opt.add(If(meet_David, 
          And(start_David >= david_available_start, 
              end_David == start_David + david_duration,
              end_David <= david_available_end),
          True))
opt.add(If(meet_Barbara, 
          And(start_Barbara >= barbara_available_start, 
              end_Barbara == start_Barbara + barbara_duration,
              end_Barbara <= barbara_available_end),
          True))

# Constraints for travel from Embarcadero to first meeting location
opt.add(If(meet_Betty,
          If(Or(And(meet_David, Not(Betty_before_David)), 
                And(meet_Barbara, Not(Betty_before_Barbara))),
                True,
                start_Betty >= start_Embarcadero + travel_dict[('Embarcadero', loc_Betty)]),
          True))

opt.add(If(meet_David,
          If(Or(And(meet_Betty, Betty_before_David), 
                And(meet_Barbara, Not(David_before_Barbara))),
                True,
                start_David >= start_Embarcadero + travel_dict[('Embarcadero', loc_David)]),
          True))

opt.add(If(meet_Barbara,
          If(Or(And(meet_Betty, Betty_before_Barbara), 
                And(meet_David, David_before_Barbara)),
                True,
                start_Barbara >= start_Embarcadero + travel_dict[('Embarcadero', loc_Barbara)]),
          True))

# Constraints for travel between meetings
opt.add(If(And(meet_Betty, meet_David),
          If(Betty_before_David,
             And(start_David >= end_Betty + travel_dict[(loc_Betty, loc_David)]),
             And(start_Betty >= end_David + travel_dict[(loc_David, loc_Betty)])),
          True))

opt.add(If(And(meet_Betty, meet_Barbara),
          If(Betty_before_Barbara,
             And(start_Barbara >= end_Betty + travel_dict[(loc_Betty, loc_Barbara)]),
             And(start_Betty >= end_Barbara + travel_dict[(loc_Barbara, loc_Betty)])),
          True))

opt.add(If(And(meet_David, meet_Barbara),
          If(David_before_Barbara,
             And(start_Barbara >= end_David + travel_dict[(loc_David, loc_Barbara)]),
             And(start_David >= end_Barbara + travel_dict[(loc_Barbara, loc_David)])),
          True))

# Objective: maximize the number of meetings
total_meetings = If(meet_Betty, 1, 0) + If(meet_David, 1, 0) + If(meet_Barbara, 1, 0)
opt.maximize(total_meetings)

# Solve the problem
if opt.check() == sat:
    m = opt.model()
    itinerary = []
    
    # Helper function to convert minutes to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{int(hours):02d}:{int(minutes):02d}"
    
    # Check and add each meeting if it happened
    meetings = []
    if is_true(m[meet_Betty]):
        start = m.eval(start_Betty).as_long()
        end = m.eval(end_Betty).as_long()
        meetings.append({
            "person": "Betty",
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    
    if is_true(m[meet_David]):
        start = m.eval(start_David).as_long()
        end = m.eval(end_David).as_long()
        meetings.append({
            "person": "David",
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    
    if is_true(m[meet_Barbara]):
        start = m.eval(start_Barbara).as_long()
        end = m.eval(end_Barbara).as_long()
        meetings.append({
            "person": "Barbara",
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x["start_time"])
    itinerary = [{"action": "meet", "person": m["person"], "start_time": m["start_time"], "end_time": m["end_time"]} for m in meetings]
    print(f'SOLUTION: {{"itinerary": {itinerary}}}')
else:
    print('SOLUTION: {"itinerary": []}')