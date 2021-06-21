from invoke import Collection, task


# pty=True added so that the tasks understand they're being run in a terminal
# and keep their pretty colored output
@task
def watch_for_mypy(c):
    c.run(
        "watchmedo shell-command --drop --command='mypy tests qcware_transpile' --recursive tests qcware_transpile",
        pty=True,
    )


@task
def mypy(c):
    c.run("mypy tests qcware_transpile", pty=True)


@task
def watch_for_tests(c, test_path="tests"):
    c.run(
        f"watchmedo shell-command --drop --command='pytest --workers auto --tests-per-worker auto {test_path}' --recursive tests qcware_transpile",
        pty=True,
    )


@task
def test(c, test_path="tests"):
    c.run(f"pytest -n auto {test_path}", pty=True)


@task
def test_serial(c, test_path="tests"):
    c.run(f"pytest {test_path}", pty=True)


watches = Collection("watch")
watches.add_task(watch_for_mypy, "mypy")
watches.add_task(watch_for_tests, "tests")

ns = Collection()
ns.add_collection(watches, "watch")
ns.add_task(test, "test")
ns.add_task(test_serial, "test_serial")
ns.add_task(mypy, "mypy")
