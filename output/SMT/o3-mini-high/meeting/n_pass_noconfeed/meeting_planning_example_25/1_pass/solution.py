from z3 import Optimize, Int, If, Or, Implies, sat
import json

def minutes_to_string(m):
    # Convert minutes (since midnight) to H:MM (24-hour) format (no leading zero for hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Input parameters (all times in minutes after midnight)
    arrival_GGP = 9 * 60           # 9:00 AM => 540
    travel_GGP_to_Chinatown = 23   # travel time in minutes

    # David's availability at Chinatown: 4:00 PM to 9:45 PM
    david_available_from = 16 * 60         # 16:00 => 960
    david_available_until = 21 * 60 + 45     # 21:45 => 1305
    min_david_meeting = 105                # minimum meeting duration with David in minutes

    # We also assume you can meet a friend at Golden Gate Park.
    # For demonstration, we call that friend "Alice". Her meeting is from your arrival time (9:00)
    # until you depart Golden Gate Park.
    
    # Create the optimizer
    opt = Optimize()
    
    # Decision variable: when to leave Golden Gate Park (in minutes after midnight).
    # To count as a meeting with Alice, we require at least 1 minute with her.
    t_depart = Int('t_depart')
    
    # Constraint: you cannot leave before you arrive.
    opt.add(t_depart >= arrival_GGP + 1)  # ensure at least one minute meeting with Alice

    # When you travel, you arrive at Chinatown at t_depart + travel_GGP_to_Chinatown.
    # For the meeting with David, if you arrive early you must wait until he is available.
    # So we define the David meeting start time as the later of (t_depart + travel) and david_available_from.
    # We do not introduce a new variable here but use an expression later.
    
    # Also, if you depart late such that you arrive after 16:00, David's meeting time shrinks.
    # In any case, his meeting must be at least min_david_meeting minutes long.
    # When arriving early (t_depart + travel < david_available_from), the meeting will start at 16:00.
    # When arriving later, it starts at t_depart + travel.
    
    # To ensure that David's meeting meets the minimum duration, we add a conditional constraint.
    # If t_depart + travel < david_available_from then his meeting duration is fixed:
    #   duration = david_available_until - david_available_from.
    # Otherwise, duration = david_available_until - (t_depart + travel).
    meeting_david_duration = If(t_depart + travel_GGP_to_Chinatown < david_available_from,
                                david_available_until - david_available_from,
                                david_available_until - (t_depart + travel_GGP_to_Chinatown))
    opt.add(meeting_david_duration >= min_david_meeting)
    
    # Also, if you arrive after David is available, you must not be so late that meeting David is impossible.
    # That is, if (t_depart + travel >= david_available_from) then we require t_depart <= david_available_until - travel_GGP_to_Chinatown - min_david_meeting.
    opt.add(Implies(t_depart + travel_GGP_to_Chinatown >= david_available_from, 
                    t_depart <= david_available_until - travel_GGP_to_Chinatown - min_david_meeting))
    
    # For constructing an objective that “maximizes meeting with as many friends as possible”,
    # we assume your goal is to maximize your total meeting time.
    # You can meet "Alice" at Golden Gate Park from your arrival until departure,
    # and "David" at Chinatown from the later of (arrival at Chinatown, David's available time) until his available until.
    meeting_alice_duration = t_depart - arrival_GGP
    meeting_david_effective = If(t_depart + travel_GGP_to_Chinatown < david_available_from,
                                 david_available_until - david_available_from,
                                 david_available_until - (t_depart + travel_GGP_to_Chinatown))
    total_meeting_time = meeting_alice_duration + meeting_david_effective
    
    # Set the optimization objective: maximize total meeting time.
    opt.maximize(total_meeting_time)
    
    # Solve the optimization problem.
    if opt.check() == sat:
        model = opt.model()
        depart_time = model[t_depart].as_long()
        
        # Determine David's meeting start time:
        # If you arrive at Chinatown before David is available, you wait until 16:00.
        david_meet_start = david_available_from if (depart_time + travel_GGP_to_Chinatown) < david_available_from else (depart_time + travel_GGP_to_Chinatown)
        
        # For maximum meeting time, it is best to finish David's meeting at his available end time.
        david_meet_end = david_available_until
        
        # Alice's meeting is from arrival at Golden Gate Park until t_depart.
        alice_meet_start = arrival_GGP
        alice_meet_end = depart_time
        
        # Prepare the itinerary as specified.
        itinerary = [
            {
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Alice",
                "start_time": minutes_to_string(alice_meet_start),
                "end_time": minutes_to_string(alice_meet_end)
            },
            {
                "action": "meet",
                "location": "Chinatown",
                "person": "David",
                "start_time": minutes_to_string(david_meet_start),
                "end_time": minutes_to_string(david_meet_end)
            }
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no valid schedule is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()