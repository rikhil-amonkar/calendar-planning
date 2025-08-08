from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Timothy is at Pacific Heights from 9:00AM to 3:30PM (min 75 minutes)
    timothy_start = Int('timothy_start')  # in minutes since 9:00AM
    timothy_end = Int('timothy_end')

    # David is at Fisherman's Wharf from 10:45AM to 3:30PM (min 15 minutes)
    david_start = Int('david_start')
    david_end = Int('david_end')

    # Robert is at Mission District from 12:15PM to 7:45PM (min 90 minutes)
    robert_start = Int('robert_start')
    robert_end = Int('robert_end')

    # Convert all times to minutes since 9:00AM (540 in 24-hour time)
    # Constraints for Timothy (Pacific Heights)
    s.add(timothy_start >= 0)  # 9:00AM is 0 minutes after 9:00AM
    s.add(timothy_end <= 390)  # 3:30PM is 390 minutes after 9:00AM (6.5 hours)
    s.add(timothy_end - timothy_start >= 75)

    # Constraints for David (Fisherman's Wharf)
    s.add(david_start >= 105)  # 10:45AM is 105 minutes after 9:00AM
    s.add(david_end <= 390)    # 3:30PM is 390 minutes
    s.add(david_end - david_start >= 15)

    # Constraints for Robert (Mission District)
    s.add(robert_start >= 195)  # 12:15PM is 195 minutes after 9:00AM
    s.add(robert_end <= 645)    # 7:45PM is 645 minutes (but we likely finish earlier)
    s.add(robert_end - robert_start >= 90)

    # Travel times (in minutes)
    # From Financial District to Pacific Heights: 13
    # So if we start with Timothy, we can meet him starting at 9:00 + 13 = 9:13
    # But Timothy is available from 9:00AM, so the earliest we can meet is 9:13AM (13 minutes after 9:00AM)
    # So Timothy's start time >= 13.

    # Assume we start by meeting Timothy first.
    # Then, the next meeting must account for travel time from Pacific Heights to the next location.

    # We need to sequence the meetings. Let's consider possible orders.

    # Possible orders: Timothy -> David -> Robert, Timothy -> Robert -> David, etc.
    # We'll model the order as a permutation and choose the one that fits.

    # Let's model the order as follows:
    # We'll have three meetings, and their start times must be after the previous end time plus travel.

    # We'll use a variable to represent the order.
    # For simplicity, we'll try all possible permutations (3! = 6 possibilities) and pick the feasible one.

    # Alternatively, we can encode the order in the constraints.

    # Let's define the order as follows:
    # 0: Timothy first, then David, then Robert
    # 1: Timothy first, then Robert, then David
    # 2: David first, then Timothy, then Robert
    # 3: David first, then Robert, then Timothy
    # 4: Robert first, then Timothy, then David
    # 5: Robert first, then David, then Timothy

    # We'll create a variable for the order and add constraints accordingly.

    # But for simplicity, let's try each order in sequence until we find a feasible solution.

    orders = [
        ['Timothy', 'David', 'Robert'],
        ['Timothy', 'Robert', 'David'],
        ['David', 'Timothy', 'Robert'],
        ['David', 'Robert', 'Timothy'],
        ['Robert', 'Timothy', 'David'],
        ['Robert', 'David', 'Timothy']
    ]

    solution_found = False
    itinerary = []

    for order in orders:
        s.push()  # create a backtracking point

        # Reset constraints for this order
        current_time = 0  # starting at 9:00AM (0 minutes)

        # Track the previous location
        prev_location = 'Financial District'

        for person in order:
            if person == 'Timothy':
                # Travel from prev_location to Pacific Heights
                travel_time = 0
                if prev_location == 'Financial District':
                    travel_time = 13
                elif prev_location == 'Fisherman\'s Wharf':
                    travel_time = 13
                elif prev_location == 'Mission District':
                    travel_time = 16
                else:
                    travel_time = 0  # shouldn't happen

                # Update current_time: arrival at Pacific Heights
                arrival_time = current_time + travel_time
                s.add(timothy_start >= arrival_time)
                s.add(timothy_start >= 0)  # already added
                s.add(timothy_end <= 390)
                s.add(timothy_end - timothy_start >= 75)

                # The meeting must be within Timothy's availability
                # Update current_time to end of meeting
                current_time = timothy_end

                # Update previous location
                prev_location = 'Pacific Heights'

            elif person == 'David':
                # Travel to Fisherman's Wharf
                travel_time = 0
                if prev_location == 'Financial District':
                    travel_time = 10
                elif prev_location == 'Pacific Heights':
                    travel_time = 12
                elif prev_location == 'Mission District':
                    travel_time = 22
                else:
                    travel_time = 0

                arrival_time = current_time + travel_time
                s.add(david_start >= arrival_time)
                s.add(david_start >= 105)  # David's availability starts at 10:45AM (105 minutes)
                s.add(david_end <= 390)
                s.add(david_end - david_start >= 15)

                current_time = david_end
                prev_location = 'Fisherman\'s Wharf'

            elif person == 'Robert':
                # Travel to Mission District
                travel_time = 0
                if prev_location == 'Financial District':
                    travel_time = 17
                elif prev_location == 'Pacific Heights':
                    travel_time = 15
                elif prev_location == 'Fisherman\'s Wharf':
                    travel_time = 22
                else:
                    travel_time = 0

                arrival_time = current_time + travel_time
                s.add(robert_start >= arrival_time)
                s.add(robert_start >= 195)  # Robert's availability starts at 12:15PM (195 minutes)
                s.add(robert_end - robert_start >= 90)

                current_time = robert_end
                prev_location = 'Mission District'

        # Check if this order is feasible
        if s.check() == sat:
            model = s.model()
            itinerary = []

            # Extract times for each person
            if 'Timothy' in order:
                t_start = model.eval(timothy_start).as_long()
                t_end = model.eval(timothy_end).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": "Timothy",
                    "start_time": f"{9 + t_start // 60:02d}:{t_start % 60:02d}",
                    "end_time": f"{9 + t_end // 60:02d}:{t_end % 60:02d}"
                })

            if 'David' in order:
                d_start = model.eval(david_start).as_long()
                d_end = model.eval(david_end).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": "David",
                    "start_time": f"{9 + d_start // 60:02d}:{d_start % 60:02d}",
                    "end_time": f"{9 + d_end // 60:02d}:{d_end % 60:02d}"
                })

            if 'Robert' in order:
                r_start = model.eval(robert_start).as_long()
                r_end = model.eval(robert_end).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": "Robert",
                    "start_time": f"{9 + r_start // 60:02d}:{r_start % 60:02d}",
                    "end_time": f"{9 + r_end // 60:02d}:{r_end % 60:02d}"
                })

            solution_found = True
            break

        s.pop()  # backtrack

    if not solution_found:
        return {"itinerary": []}

    return {"itinerary": itinerary}

# Execute the solver
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))