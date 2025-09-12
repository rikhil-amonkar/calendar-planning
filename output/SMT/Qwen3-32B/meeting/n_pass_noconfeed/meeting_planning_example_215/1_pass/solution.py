from z3 import *
import json

def main():
    friends = [
        {
            'name': 'Jason',
            'location': "Fisherman's Wharf",
            'available_start': 960,  # 4:00 PM
            'available_end': 1005,   # 4:45 PM
            'min_duration': 30
        },
        {
            'name': 'Jessica',
            'location': 'Embarcadero',
            'available_start': 1005,  # 4:45 PM
            'available_end': 1140,    # 7:00 PM
            'min_duration': 30
        },
        {
            'name': 'Sandra',
            'location': 'Richmond District',
            'available_start': 1110,  # 6:30 PM
            'available_end': 1305,    # 9:45 PM
            'min_duration': 120
        }
    ]

    friend_travel_times = [
        [0, 6, 18],   # From Fisherman's Wharf (0)
        [8, 0, 21],   # From Embarcadero (1)
        [18, 19, 0]   # From Richmond District (2)
    ]

    solver = Solver()

    first = Int('first')
    second = Int('second')
    third = Int('third')

    solver.add(And(0 <= first, first <= 2))
    solver.add(And(0 <= second, second <= 2))
    solver.add(And(0 <= third, third <= 2))
    solver.add(Distinct(first, second, third))

    # Step 0: Bayview to first
    travel_time_0 = If(first == 0, 25, If(first == 1, 19, 25))
    arrival_time_0 = 540 + travel_time_0  # 9:00 AM = 540 minutes

    available_start_0 = If(first == 0, 960, If(first == 1, 1005, 1110))
    available_end_0 = If(first == 0, 1005, If(first == 1, 1140, 1305))
    min_duration_0 = If(first == 0, 30, If(first == 1, 30, 120))

    start_time_0 = If(arrival_time_0 >= available_start_0, arrival_time_0, available_start_0)
    end_time_0 = start_time_0 + min_duration_0
    solver.add(end_time_0 <= available_end_0)

    # Step 1: first to second
    travel_time_1 = If(
        first == 0,
        If(second == 1, 6, If(second == 2, 18, 0)),
        If(first == 1,
           If(second == 0, 8, If(second == 2, 21, 0)),
           If(first == 2,
              If(second == 0, 18, If(second == 1, 19, 0)),
              0
           )
        )
    )
    arrival_time_1 = end_time_0 + travel_time_1

    available_start_1 = If(second == 0, 960, If(second == 1, 1005, 1110))
    available_end_1 = If(second == 0, 1005, If(second == 1, 1140, 1305))
    min_duration_1 = If(second == 0, 30, If(second == 1, 30, 120))

    start_time_1 = If(arrival_time_1 >= available_start_1, arrival_time_1, available_start_1)
    end_time_1 = start_time_1 + min_duration_1
    solver.add(end_time_1 <= available_end_1)

    # Step 2: second to third
    travel_time_2 = If(
        second == 0,
        If(third == 1, 6, If(third == 2, 18, 0)),
        If(second == 1,
           If(third == 0, 8, If(third == 2, 21, 0)),
           If(second == 2,
              If(third == 0, 18, If(third == 1, 19, 0)),
              0
           )
        )
    )
    arrival_time_2 = end_time_1 + travel_time_2

    available_start_2 = If(third == 0, 960, If(third == 1, 1005, 1110))
    available_end_2 = If(third == 0, 1005, If(third == 1, 1140, 1305))
    min_duration_2 = If(third == 0, 30, If(third == 1, 30, 120))

    start_time_2 = If(arrival_time_2 >= available_start_2, arrival_time_2, available_start_2)
    end_time_2 = start_time_2 + min_duration_2
    solver.add(end_time_2 <= available_end_2)

    if solver.check() == sat:
        model = solver.model()
        f = model[first].as_long()
        s = model[second].as_long()
        t = model[third].as_long()

        itinerary = []
        for i, friend_idx in enumerate([f, s, t]):
            friend = friends[friend_idx]
            if i == 0:
                st = model.eval(start_time_0).as_long()
                et = model.eval(end_time_0).as_long()
            elif i == 1:
                st = model.eval(start_time_1).as_long()
                et = model.eval(end_time_1).as_long()
            else:
                st = model.eval(start_time_2).as_long()
                et = model.eval(end_time_2).as_long()

            def to_time_str(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"

            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": to_time_str(st),
                "end_time": to_time_str(et)
            })

        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()