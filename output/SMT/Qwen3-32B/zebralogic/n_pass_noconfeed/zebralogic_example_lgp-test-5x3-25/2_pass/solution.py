# Check solution
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": []
        }
    }
    for i in range(5):
        house_num = i + 1
        name_val = model.eval(names[i]).decl().name()
        height_val = model.eval(heights[i]).decl().name()
        food_val = model.eval(foods[i]).decl().name()
        solution["solution"]["rows"].append([str(house_num), name_val, height_val, food_val])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")