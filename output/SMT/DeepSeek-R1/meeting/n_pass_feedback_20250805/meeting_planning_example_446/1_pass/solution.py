from z3 import *
import json

def main():
    # Travel time matrix: 6x6, index 0:Richmond, 1:Bayview, 2:Chinatown, 3:Financial, 4:Marina, 5:Union Square
    T = [
        [0, 26, 20, 22, 9, 21],   # from Richmond
        [25, 0, 18, 19, 25, 17],   # from Bayview
        [20, 22, 0, 5, 12, 7],     # from Chinatown
        [21, 19, 5, 0, 15, 9],     # from Financial
        [11, 25, 16, 17, 0, 16],   # from Marina
        [20, 15, 7, 9, 18, 0]      # from Union Square
    ]

    meetings = [1, 2, 3, 4, 5]  # Bayview, Chinatown, Financial, Marina, Union Square
    names = {
        1: "Margaret",
        2: "Robert",
        3: "Rebecca",
        4: "Kimberly",
        5: "Kenneth"
    }
    durations = {
        1: 30,   # Margaret
        2: 15,   # Robert
        3: 75,   # Rebecca
        4: 15,   # Kimberly
        5: 75    # Kenneth
    }
    availability = {
        1: (30, 270),    # Margaret: 9:30 AM to 1:30 PM
        2: (195, 675),   # Robert: 12:15 PM to 8:15 PM
        3: (255, 465),   # Rebecca: 1:15 PM to 4:45 PM
        4: (255, 465),   # Kimberly
        5: (630, 735)    # Kenneth: 7:30 PM to 9:15 PM
    }

    s = Solver()

    start_vars = { m: Int(f'start_{m}') for m in meetings }
    order_vars = { m: Int(f'order_{m}') for m in meetings }

    s.add(Distinct([order_vars[m] for m in meetings]))
    for m in meetings:
        s.add(order_vars[m] >= 0, order_vars[m] < 5)

    for m in meetings:
        s.add(start_vars[m] >= availability[m][0])
        s.add(start_vars[m] + durations[m] <= availability[m][1])

    for m in meetings:
        s.add(Implies(order_vars[m] == 0, start_vars[m] >= T[0][m]))

    for i in meetings:
        for j in meetings:
            if i != j:
                s.add(Implies(order_vars[j] == order_vars[i] + 1, 
                              start_vars[i] + durations[i] + T[i][j] <= start_vars[j]))

    for m in meetings:
        s.add(start_vars[m] >= 0)

    if s.check() == sat:
        model = s.model()
        start_times = {}
        for m in meetings:
            start_val = model.evaluate(start_vars[m]).as_long()
            start_times[m] = start_val

        itinerary = []
        for m in meetings:
            total_minutes = start_times[m]
            hours = 9 + total_minutes // 60
            minutes = total_minutes % 60
            start_time = f"{hours:02d}:{minutes:02d}"
            
            end_minutes = total_minutes + durations[m]
            hours_end = 9 + end_minutes // 60
            minutes_end = end_minutes % 60
            end_time = f"{hours_end:02d}:{minutes_end:02d}"
            
            itinerary.append({
                "action": "meet",
                "person": names[m],
                "start_time": start_time,
                "end_time": end_time
            })
        
        itinerary.sort(key=lambda x: x['start_time'])
        
        output = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(output))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()