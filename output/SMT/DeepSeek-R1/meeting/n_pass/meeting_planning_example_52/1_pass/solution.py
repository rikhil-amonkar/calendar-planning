import z3
import json

def main():
    # Convert time strings to minutes since midnight
    start_at_russian_hill = 9 * 60  # 9:00 AM in minutes (540)
    barbara_available_start = 13 * 60 + 15  # 13:15 (795)
    barbara_available_end = 18 * 60 + 15    # 18:15 (1095)
    travel_to_richmond = 14  # minutes

    # Create Z3 variables
    s = z3.Optimize()
    start = z3.Int('start')
    end = z3.Int('end')
    departure = z3.Int('departure')  # when we leave Russian Hill

    # Constraints
    s.add(departure >= start_at_russian_hill)
    s.add(departure + travel_to_richmond <= start)
    s.add(start >= barbara_available_start)
    s.add(end <= barbara_available_end)
    s.add(end == start + 45)  # exactly 45 minutes meeting

    # Minimize the start time to meet as early as possible
    s.minimize(start)

    if s.check() == z3.sat:
        m = s.model()
        start_val = m[start].as_long()
        end_val = m[end].as_long()

        # Format the times to HH:MM
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        start_str = format_time(start_val)
        end_str = format_time(end_val)

        itinerary = [
            {"action": "meet", "person": "Barbara", "start_time": start_str, "end_time": end_str}
        ]
        result = {"itinerary": itinerary}
        # Output as JSON string
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')  # no solution found

if __name__ == '__main__':
    main()