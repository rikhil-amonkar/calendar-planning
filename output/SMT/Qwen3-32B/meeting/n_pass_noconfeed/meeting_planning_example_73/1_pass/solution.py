import z3
import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Convert times to minutes since midnight
    arrival_russian_hill = 9 * 60  # 9:00 AM → 540
    barbara_start = 7 * 60 + 15  # 7:15 AM → 435
    barbara_end = 22 * 60  # 10:00 PM → 1320
    travel_time = 7  # minutes
    min_meeting_duration = 60  # minutes

    # Earliest arrival at Pacific Heights is arrival time at Russian Hill + travel time
    earliest_pacific_arrival = arrival_russian_hill + travel_time  # 540 +7 = 547

    # Variables for meeting with Barbara
    t_start = z3.Int('t_start')
    t_end = z3.Int('t_end')

    opt = z3.Optimize()

    # Constraints
    opt.add(t_start >= earliest_pacific_arrival)
    opt.add(t_end >= t_start + min_meeting_duration)
    opt.add(t_end <= barbara_end)

    # Optimize for earliest start time
    opt.minimize(t_start)

    # Check if solution exists
    if opt.check() == z3.sat:
        model = opt.model()
        start_time_min = model[t_start].as_long()
        end_time_min = model[t_end].as_long()

        # Convert to time strings
        start_time_str = minutes_to_time(start_time_min)
        end_time_str = minutes_to_time(end_time_min)

        # Build the itinerary
        itinerary = [{
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Barbara",
            "start_time": start_time_str,
            "end_time": end_time_str
        }]

        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # No solution found
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()