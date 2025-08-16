from z3 import Optimize

def format_time(t):
    # t is in minutes since midnight; convert to HH:MM (24-hour)
    hours = t // 60
    minutes = t % 60
    return f"{hours:02d}:{minutes:02d}"

def schedule():
    opt = Optimize()

    # Constants (in minutes since midnight)
    arrival_russian_hill = 9 * 60      # 09:00 = 540 minutes
    travel_RH_to_RD = 14               # minutes from Russian Hill to Richmond District
    barbara_avail_start = 13 * 60 + 15  # 13:15 = 795 minutes
    barbara_avail_end = 18 * 60 + 15    # 18:15 = 1095 minutes
    min_meeting_duration = 45          # minutes

    # Decision variables: meeting start and end times with Barbara (in minutes since midnight).
    barbara_start =  opt.Int('barbara_start')
    barbara_end = opt.Int('barbara_end')

    # Constraints:
    # You have to start at Russian Hill at 9:00, so the earliest you can reach Richmond District is 9:00 + travel time.
    earliest_arrival_RD = arrival_russian_hill + travel_RH_to_RD
    # But Barbara is only available starting at barbara_avail_start.
    # So meeting with Barbara can only start at or after the later of these two times.
    opt.add(barbara_start >= barbara_avail_start)
    # Meeting must end by the end of Barbara's availability.
    opt.add(barbara_end <= barbara_avail_end)
    # Meeting duration must be at least 45 minutes.
    opt.add(barbara_end >= barbara_start + min_meeting_duration)

    # To maximize our day, we want to meet Barbara as early as possible (so that we have more time for other meetings later).
    # We add an objective to minimize the start time of the meeting.
    opt.minimize(barbara_start)

    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        bs = model[barbara_start].as_long()
        be = model[barbara_end].as_long()

        # Format times in HH:MM (24-hour format)
        meeting_entry = {
            "action": "meet",
            "person": "Barbara",
            "start_time": format_time(bs),
            "end_time": format_time(be)
        }
        itinerary = {"itinerary": [meeting_entry]}
        print(itinerary)
        return itinerary
    else:
        print("No solution found")
        return None

if __name__ == '__main__':
    schedule()