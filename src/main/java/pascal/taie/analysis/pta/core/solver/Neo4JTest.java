package pascal.taie.analysis.pta.core.solver;

import org.neo4j.driver.*;

import static org.neo4j.driver.Values.parameters;

public class Neo4JTest implements AutoCloseable {
    private final Driver driver;
    private Session session;
    public Neo4JTest(String uri, String user, String password) {
        driver = GraphDatabase.driver(uri, AuthTokens.basic(user, password));
        session = driver.session();
    }

    @Override
    public void close() throws RuntimeException {
        driver.close();
    }

    public void addRelation(String name1, String name2) {
//        var session = driver.session();
        var query = new Query("MERGE (r:Person {name:$name1}) MERGE (s:Person {name:$name2}) MERGE (r)-[:FRIEND_OF]->(s)",
                parameters("name1", name1, "name2", name2));
        session.run(query);
    }

    public void printGreeting(final String message) {
        try (var session = driver.session()) {
            var greeting = session.executeWrite(tx -> {
                var query = new Query("CREATE (a:Greeting) SET a.message = $message RETURN a.message + ', from node ' + id(a)", parameters("message", message));
                var result = tx.run(query);
                return result.single().get(0).asString();
            });
            System.out.println(greeting);
        }
    }
//    public void addConstrain() {
//        var session = driver.session();
//        var query = new Query("CREATE CONSTRAINT uniqueNode FOR (node:Node) REQUIRE node.name IS UNIQUE");
//        session.run(query);
//    }

    public static void main(String... args) {
        try (var greeter = new Neo4JTest("bolt://localhost:7687", "neo4j", "password")) {
//            greeter.printGreeting("hello, world");
            greeter.addRelation("var1", "var2");
            greeter.addRelation("var1", "var3");
        }
    }
}
