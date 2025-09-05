import json
from z3 import *

def format_time(minutes):
    # Our internal clock counts minutes since 9:00.
    # 9:00 is 9*60 = 540 minutes in absolute minutes.
    total = 540 + minutes
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()

    # Decision booleans: whether to meet each friend.
    meet_emily   = Bool("meet_emily")
    meet_barbara = Bool("meet_barbara")
    meet_william = Bool("meet_william")

    # Time variables are measured in minutes after 9:00.
    # For each meeting we have a start time and an end time.
    s_emily   = Int("s_emily")
    e_emily   = Int("e_emily")
    s_barbara = Int("s_barbara")
    e_barbara = Int("e_barbara")
    s_william = Int("s_william")
    e_william = Int("e_william")

    # Travel times (in minutes) between locations:
    # Castro -> Alamo Square: 8
    # Castro -> Union Square: 19
    # Castro -> Chinatown: 20
    # Alamo Square -> Union Square: 14
    # Alamo Square -> Chinatown: 16
    # Union Square -> Chinatown: 7
    # (Other directions not needed as our itinerary always departs from Castro and then goes to one other friend after Emily.)
    
    # Availability windows (in minutes since 9:00):
    # Emily is available at Alamo Square from 11:45 to 15:15.
    #    11:45 = 9:00 + 165, 15:15 = 9:00 + 375.
    # Barbara is available at Union Square from 16:45 to 18:15.
    #    16:45 = 9:00 + 465, 18:15 = 9:00 + 555.
    # William is available at Chinatown from 17:15 to 19:00.
    #    17:15 = 9:00 + 495, 19:00 = 9:00 + 600.

    # Meeting minimum durations:
    # Emily: at least 105 minutes.
    # Barbara: at least 60 minutes.
    # William: at least 105 minutes.

    # Constraints for Emily's meeting at Alamo Square:
    opt.add(Implies(meet_emily, s_emily >= 165))   # Must start no earlier than 11:45.
    opt.add(Implies(meet_emily, e_emily <= 375))     # Must finish by 15:15.
    opt.add(Implies(meet_emily, e_emily - s_emily >= 105))
    # In order to allow a meeting of at least 105 minutes before 15:15, the start must be at most 270.
    opt.add(Implies(meet_emily, s_emily <= 270))

    # Constraints for Barbara's meeting at Union Square:
    opt.add(Implies(meet_barbara, s_barbara >= 465))   # Must start no earlier than 16:45.
    opt.add(Implies(meet_barbara, s_barbara <= 495))     # To allow 60 min meeting ending by 18:15.
    opt.add(Implies(meet_barbara, e_barbara <= 555))     # Must finish by 18:15.
    opt.add(Implies(meet_barbara, e_barbara - s_barbara >= 60))

    # Constraints for William's meeting at Chinatown:
    # Because his available window is exactly 105 minutes, we force the meeting.
    opt.add(Implies(meet_william, s_william == 495))   # Must start exactly at 17:15.
    opt.add(Implies(meet_william, e_william == 600))     # Must finish exactly at 19:00.

    # If a meeting is chosen it must be reachable from Castro.
    # Castro to Alamo: 8, to Union: 19, to Chinatown: 20.
    # (These are automatically satisfied because the availability windows start well after these travel times.)

    # Ordering constraints:
    # If we meet both Emily and Barbara, then after finishing Emily we must have time to travel from Alamo to Union Square.
    opt.add(Implies(And(meet_emily, meet_barbara), e_emily + 14 <= s_barbara))
    # If we meet both Emily and William, then after finishing Emily we must have time to travel from Alamo to Chinatown.
    opt.add(Implies(And(meet_emily, meet_william), e_emily + 16 <= s_william))
    # Barbara and William cannot both be met because their time windows overlap and travel makes it impossible.
    opt.add(Not(And(meet_barbara, meet_william)))

    # Our objective: maximize number of meetings, then maximize total meeting time.
    friend_count = If(meet_emily, 1, 0) + If(meet_barbara, 1, 0) + If(meet_william, 1, 0)
    total_meeting_time = If(meet_emily, e_emily - s_emily, 0) + \
                         If(meet_barbara, e_barbara - s_barbara, 0) + \
                         If(meet_william, e_william - s_william, 0)

    # The primary goal is to meet as many friends as possible.
    # The secondary goal is to maximize the total meeting time.
    h1 = opt.maximize(friend_count)
    h2 = opt.maximize(total_meeting_time)

    if opt.check() == sat:
        model = opt.model()

        # Build the itinerary from the model.
        events = []
        if is_true(model.evaluate(meet_emily)):
            start = model[s_emily].as_long()
            end = model[e_emily].as_long()
            events.append((start, {
                "action": "meet",
                "location": "Alamo Square",
                "person": "Emily",
                "start_time": format_time(start),
                "end_time": format_time(end)
            }))
        if is_true(model.evaluate(meet_barbara)):
            start = model[s_barbara].as_long()
            end = model[e_barbara].as_long()
            events.append((start, {
                "action": "meet",
                "location": "Union Square",
                "person": "Barbara",
                "start_time": format_time(start),
                "end_time": format_time(end)
            }))
        if is_true(model.evaluate(meet_william)):
            start = model[s_william].as_long()
            end = model[e_william].as_long()
            events.append((start, {
                "action": "meet",
                "location": "Chinatown",
                "person": "William",
                "start_time": format_time(start),
                "end_time": format_time(end)
            }))

        # Sort events by their start times.
        events.sort(key=lambda x: x[0])
        itinerary = [event for _, event in events]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()