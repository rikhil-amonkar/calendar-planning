from z3 import *

def main():
    s = Solver()
    days = 20
    cities = ["Athens", "Valencia", "Zurich", "Naples"]
    A = [Bool(f"A_{i+1}") for i in range(days)]
    V = [Bool(f"V_{i+1}") for i in range(days)]
    Z = [Bool(f"Z_{i+1}") for i in range(days)]
    N = [Bool(f"N_{i+1}") for i in range(days)]
    all_cities = [A, V, Z, N]

    # At least one city per day and at most two
    for i in range(days):
        s.add(Or(A[i], V[i], Z[i], N[i]))
        s.add(AtMost(A[i], V[i], Z[i], N[i], 2))

    # Total days per city
    s.add(Sum([If(A[i], 1, 0) for i in range(days)]) == 6)
    s.add(Sum([If(V[i], 1, 0) for i in range(days)]) == 6)
    s.add(Sum([If(Z[i], 1, 0) for i in range(days)]) == 6)
    s.add(Sum([If(N[i], 1, 0) for i in range(days)]) == 5)

    # Athens on days 1-6 and Naples on days 16-20
    for i in range(6):
        s.add(A[i] == True)
    for i in range(15, 20):
        s.add(N[i] == True)

    # Only Athens on days 1-5 and only Naples on days 17-20
    for i in range(5):
        s.add(And(V[i] == False, Z[i] == False, N[i] == False))
    for i in range(16, 20):
        s.add(And(A[i] == False, V[i] == False, Z[i] == False))

    # Only Naples on day 20
    s.add(And(A[19] == False, V[19] == False, Z[19] == False))

    # Transition constraint: consecutive days must share at least one city
    for i in range(days - 1):
        s.add(Or(
            And(A[i], A[i+1]),
            And(V[i], V[i+1]),
            And(Z[i], Z[i+1]),
            And(N[i], N[i+1])
        ))

    # Only Athens on day 1
    s.add(And(V[0] == False, Z[0] == False, N[0] == False))

    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for i in range(days):
            day_cities = []
            if is_true(m[A[i]]):
                day_cities.append("Athens")
            if is_true(m[V[i]]):
                day_cities.append("Valencia")
            if is_true(m[Z[i]]):
                day_cities.append("Zurich")
            if is_true(m[N[i]]):
                day_cities.append("Naples")
            day_cities.sort()
            itinerary_list.append({"day": i+1, "city": ", ".join(day_cities)})
        result = {"itinerary": itinerary_list}
        import json
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()