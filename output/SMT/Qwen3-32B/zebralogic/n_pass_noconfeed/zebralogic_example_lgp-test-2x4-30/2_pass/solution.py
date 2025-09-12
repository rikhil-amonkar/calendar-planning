if solver.check() == sat:
    model = solver.model()
    # Extract values for house 1 and 2
    n1 = str(model[name1])
    h1 = str(model[hair1])
    s1 = str(model[sport1])
    sm1 = str(model[smoothie1])

    n2 = str(model[name2])
    h2 = str(model[hair2])
    s2 = str(model[sport2])
    sm2 = str(model[smoothie2])

    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
            "rows": [
                ["1", n1, h1, s1, sm1],
                ["2", n2, h2, s2, sm2]
            ]
        }
    }

    print(json.dumps(solution, indent=2))
else:
    print(json.dumps({"error": "No solution found"}, indent=2))